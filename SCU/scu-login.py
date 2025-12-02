import os
import time
import requests
import execjs

from captcha_ocr import solve_captcha_from_base64, save_captcha_to_file


ACCOUNT = "your_id_here"
PASSWORD = "your_password_here"

SM2_JS_PATH = os.path.join(os.path.dirname(__file__), "sm2_all.js")

CAPTCHA_URL = "https://id.scu.edu.cn/api/public/bff/v1.2/one_time_login/captcha"
SM2_KEY_URL = "https://id.scu.edu.cn/api/public/bff/v1.2/sm2_key"
REST_TOKEN_URL = "https://id.scu.edu.cn/api/public/bff/v1.2/rest_token"


def load_sm2():
    """加载 sm2_all.js 并返回 JS 上下文"""
    bootstrap_js = r"""
    var window = this;
    var navigator = { appName: "Netscape" };
    var console = { log: function(){}, error: function(){}, warn: function(){} };
    """

    with open(SM2_JS_PATH, "r", encoding="utf-8") as f:
        sm2_js_code = f.read()

    helper_js = """
    function sm2EncryptB64(publicKey, plaintext) {
        var result = SM2.encryptUseB64(publicKey, plaintext);
        return result.b64;
    }
    """

    return execjs.compile(bootstrap_js + sm2_js_code + helper_js)


def encrypt_password(ctx, public_key_b64: str, plaintext: str) -> str:
    """使用 sm2_all.js 进行 SM2 加密"""
    return ctx.call("sm2EncryptB64", public_key_b64, plaintext)


def fetch_captcha(
    session: requests.Session,
    auto_ocr: bool = True,
    fallback_manual: bool = True,
):
    """获取验证码并返回 (cap_code, cap_text)"""
    ts = int(time.time() * 1000)
    params = {"_enterprise_id": "scdx", "timestamp": str(ts)}

    resp = session.get(CAPTCHA_URL, params=params, timeout=10)
    resp.raise_for_status()
    data = resp.json()["data"]

    cap_code = data["code"]
    cap_b64 = data["captcha"]

    if auto_ocr:
        cap_text = solve_captcha_from_base64(
            cap_b64,
            spread_thresh=10,
            threshold=128,
        )
        # 如果识别失败（为空或长度不是4），保存本地后手动输入
        if fallback_manual and (not cap_text or len(cap_text) != 4):
            print(f"[!] 验证码识别失败: {cap_text}")
            save_captcha_to_file(cap_b64)
            cap_text = input("手动输入验证码: ").strip()
    else:
        save_captcha_to_file(cap_b64)
        cap_text = input("请输入验证码: ").strip()

    return cap_code, cap_text


def fetch_sm2_key(session: requests.Session):
    """获取 sm2_code 和 SM2 公钥"""
    resp = session.post(SM2_KEY_URL, json={}, timeout=10)
    resp.raise_for_status()
    data = resp.json()["data"]
    return data["code"], data["publicKey"]


def request_token(
    session: requests.Session,
    username: str,
    password_cipher_b64: str,
    sm2_code: str,
    cap_code: str,
    cap_text: str,
):
    """调用 rest_token 接口"""
    payload = {
        "client_id": "1371cbeda563697537f28d99b4744a973uDKtgYqL5B",
        "grant_type": "password",
        "scope": "read",
        "username": username,
        "password": password_cipher_b64,
        "_enterprise_id": "scdx",
        "sm2_code": sm2_code,
        "cap_code": cap_code,
        "cap_text": cap_text,
    }

    headers = {
        "Origin": "https://id.scu.edu.cn",
        "Referer": "https://id.scu.edu.cn/",
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/120.0.0.0 Safari/537.36"
        ),
    }

    resp = session.post(
        REST_TOKEN_URL,
        json=payload,
        headers=headers,
        timeout=10,
        allow_redirects=True,
    )

    try:
        j = resp.json()
        print("[+] rest_token JSON 响应:", j)
    except ValueError:
        print("[+] rest_token 原始响应:", resp.text)

    return resp


def login():
    ctx = load_sm2()

    with requests.Session() as session:
        # 验证码 + OCR
        cap_code, cap_text = fetch_captcha(session)
        print("[*] captcha OCR:", cap_text)

        # SM2 公钥
        sm2_code, public_key_b64 = fetch_sm2_key(session)

        # 加密密码
        cipher_pwd = encrypt_password(ctx, public_key_b64, PASSWORD)

        # 调用登录接口
        resp = request_token(
            session,
            username=ACCOUNT,
            password_cipher_b64=cipher_pwd,
            sm2_code=sm2_code,
            cap_code=cap_code,
            cap_text=cap_text,
        )

        print("[*] status:", resp.status_code)
        print("[*] final URL:", resp.url)

        # JSON 中 success=True 且 code='200' 算作成功
        ok = False
        if resp.status_code == 200:
            try:
                j = resp.json()
                if (
                    isinstance(j, dict)
                    and j.get("success") is True
                    and j.get("code") == "200"
                ):
                    ok = True
            except ValueError:
                # 如果不是 JSON，就认为失败
                ok = False

        if ok:
            print("[+] 登录成功")
        else:
            print("[!] 看起来登录失败了")


if __name__ == "__main__":
    login()
