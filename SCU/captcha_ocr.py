# -*- coding: utf-8 -*-
import base64
import io
import os
from typing import Optional
import numpy as np
from PIL import Image
import easyocr


def clean_captcha_image(
    img: Image.Image,
    spread_thresh: int = 10,
    threshold: int = 128,
) -> Image.Image:
    
    # 转为 RGB
    img_rgb = img.convert("RGB")
    arr = np.array(img_rgb)  # (H, W, 3)
    h, w, _ = arr.shape

    # 统计所有颜色与数量
    flat = arr.reshape(-1, 3)
    colors, counts = np.unique(flat, axis=0, return_counts=True)

    # 背景色：出现次数最多的颜色
    bg_idx = int(np.argmax(counts))
    bg_color = tuple(colors[bg_idx])

    # 干扰线颜色：非背景中，接近灰色(三通道差值小)且数量最多
    line_idx: Optional[int] = None
    max_cnt = -1
    for i, (c, cnt) in enumerate(zip(colors, counts)):
        if i == bg_idx:
            continue
        r, g, b = c
        spread = int(max(c) - min(c))
        if spread <= spread_thresh:  # 接近灰色
            if cnt > max_cnt:
                max_cnt = cnt
                line_idx = i

    line_color = tuple(colors[line_idx]) if line_idx is not None else None

    # 构造掩码
    bg_mask = (
        (arr[:, :, 0] == bg_color[0]) &
        (arr[:, :, 1] == bg_color[1]) &
        (arr[:, :, 2] == bg_color[2])
    )

    if line_color is not None:
        line_mask = (
            (arr[:, :, 0] == line_color[0]) &
            (arr[:, :, 1] == line_color[1]) &
            (arr[:, :, 2] == line_color[2])
        )
    else:
        line_mask = np.zeros((h, w), dtype=bool)

    # 剩余像素全部视为字符
    char_mask = ~(bg_mask | line_mask)

    # 灰度图
    gray = np.array(img_rgb.convert("L"))

    # 强行设定前景/背景
    # 字符为黑0，背景和干扰线为白255
    gray2 = gray.copy()
    gray2[char_mask] = 0
    gray2[~char_mask] = 255

    # 再做一次阈值二值化
    binary = np.where(gray2 < threshold, 0, 255).astype(np.uint8)

    # 返回结果图
    out_img = Image.fromarray(binary, mode="L")
    return out_img


def _image_from_base64(b64_str: str) -> Image.Image:
    """
    从 base64 字符串构造 PIL.Image。
    """
    # 去掉 data URL 前缀
    if "," in b64_str and "base64" in b64_str[: b64_str.index(",") + 1]:
        b64_str = b64_str.split(",", 1)[1]

    img_bytes = base64.b64decode(b64_str)
    return Image.open(io.BytesIO(img_bytes))

_reader = None

def _get_ocr_reader():
    """获取或初始化 OCR 识别器"""
    global _reader
    if _reader is None:
        # 禁用 easyocr 的 GPU 提示信息
        from contextlib import redirect_stdout, redirect_stderr
        with redirect_stdout(open(os.devnull, 'w')), redirect_stderr(open(os.devnull, 'w')):
            _reader = easyocr.Reader(['en'], gpu=False)
    return _reader


def ocr_image(
    img: Image.Image,
    languages: list = None,
) -> str:
    """
    对单张图像执行英文 OCR。
    """
    if languages is None:
        languages = ['en']
    reader = _get_ocr_reader()
    # 将 PIL Image 转换为 numpy array
    img_array = np.array(img)
    results = reader.readtext(img_array)
    # 提取识别文本并拼接
    text = ''.join([result[1] for result in results])
    return text.strip().replace(' ', '')


def solve_captcha_from_base64(
    b64_str: str,
    spread_thresh: int = 10,
    threshold: int = 128,
    languages: list = None,
) -> str:

    img = _image_from_base64(b64_str)
    clean_img = clean_captcha_image(img, spread_thresh=spread_thresh, threshold=threshold)
    text = ocr_image(clean_img, languages=languages)
    return text


def solve_captcha_from_file(
    path: str,
    spread_thresh: int = 10,
    threshold: int = 128,
    languages: list = None,
) -> str:
    """
    辅助封装：从本地文件路径读取验证码图片，处理并 OCR。
    """
    img = Image.open(path)
    clean_img = clean_captcha_image(img, spread_thresh=spread_thresh, threshold=threshold)
    text = ocr_image(clean_img, languages=languages)
    return text


def save_captcha_to_file(
    b64_str: str,
    path: str = "captcha.png",
) -> None:
    """
    将 base64 验证码图片保存到本地文件。
    """
    img = _image_from_base64(b64_str)
    img.save(path)
    print(f"[!] 验证码已保存到: {path}")


if __name__ == "__main__":
    # 简单测试，当前目录下有 captcha.png
    try:
        result = solve_captcha_from_file("captcha.png")
        print("OCR Result:", result)
    except Exception as e:
        print("Test failed:", e)
