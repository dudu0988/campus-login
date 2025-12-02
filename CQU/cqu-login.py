# -*- coding: utf-8 -*-
import base64
import requests
from bs4 import BeautifulSoup
from Crypto.Cipher import DES
from Crypto.Util.Padding import pad


LOGIN_URL = "https://sso.cqu.edu.cn/login"

USERNAME = "your_id_here"
PASSWORD = "your_password_here"


def encrypt_password(plaintext: str, key_b64: str) -> str:
    """使用 DES-ECB-PKCS7 加密密码"""
    key = base64.b64decode(key_b64)   # login-croypto 里的 Base64
    cipher = DES.new(key, DES.MODE_ECB)
    padded = pad(plaintext.encode("utf-8"), 8)  # PKCS7(block=8)
    ct = cipher.encrypt(padded)
    return base64.b64encode(ct).decode("ascii")


def get_login_page(session: requests.Session):
    """GET 登录页并解析需要的字段"""
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/122.0 Safari/537.36"
        )
    }
    resp = session.get(LOGIN_URL, headers=headers)
    resp.raise_for_status()

    soup = BeautifulSoup(resp.text, "lxml")

    def get_p(id_):
        tag = soup.find("p", id=id_)
        return tag.get_text(strip=True) if tag else ""

    current_type = get_p("current-login-type")     # 一般是 UsernamePassword
    login_crypto = get_p("login-croypto")          # DES key (Base64)
    login_rule_type = get_p("login-rule-type")     # normal / ?
    flowkey = get_p("login-page-flowkey")          # 用作 execution
    redirect_uri = get_p("redirect-uri")           # 视情况使用
    login_back_uri = get_p("login-back-uri")       # 一般是回跳地址编码后

    return {
        "current_type": current_type,
        "login_crypto": login_crypto,
        "login_rule_type": login_rule_type,
        "flowkey": flowkey,
        "redirect_uri": redirect_uri,
        "login_back_uri": login_back_uri,
    }


def login():
    with requests.Session() as session:
        # 1. 访问登录页，拿到各种参数
        meta = get_login_page(session)
        # print("[*] current-login-type:", meta["current_type"])
        # print("[*] login-croypto key:", meta["login_crypto"])
        # print("[*] login-page-flowkey (execution):", meta["flowkey"])

        if not meta["login_crypto"] or not meta["flowkey"]:
            raise RuntimeError("无法从页面中解析 login-croypto 或 login-page-flowkey")

        # 2. 用 login-croypto 做 DES 加密密码
        encrypted_pwd = encrypt_password(
            PASSWORD,
            meta["login_crypto"],
        )
        # print("[*] encrypted password:", encrypted_pwd)

        # 3. 构造 POST 的表单数据
        # username=<用户名>&type=UsernamePassword&_eventId=submit
        # &geolocation=&execution=<UUID>_<GZIP+Base64>&captcha_code=
        # &croypto=<login-croypto>&password=DKqIw6I%2BN1c%3D
        data = {
            "username": USERNAME,
            "type": meta["current_type"] or "UsernamePassword",
            "_eventId": "submit",
            "geolocation": "",
            "execution": meta["flowkey"],           # <UUID>_<GZIP+Base64>
            "captcha_code": "",
            "croypto": meta["login_crypto"],        # 页面里的 login-croypto
            "password": encrypted_pwd,              # DES 加密后 Base64
        }

        headers = {
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/122.0 Safari/537.36"
            ),
            "Referer": LOGIN_URL,
            "Origin": "https://sso.cqu.edu.cn",
        }

        # 4. 提交登录
        resp = session.post(LOGIN_URL, data=data, headers=headers, allow_redirects=True)
        print("[*] status:", resp.status_code)
        print("[*] final URL:", resp.url)

        # 简单判断一下是否登录成功
        if "login-error-code" in resp.text or "Bad credentials" in resp.text:
            print("[!] 看起来登录失败了")
        else:
            print("[+] 登录成功")

        # 后续访问示例：
        # r2 = session.get(resp.url, headers=headers)
        # print(r2.text[:1000])


if __name__ == "__main__":
    login()
