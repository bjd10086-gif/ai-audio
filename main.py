from __future__ import annotations

import asyncio
import base64
import random
import hashlib
import hmac
import io
import json
import logging
import os
import re
import secrets
import smtplib
import subprocess
import sys
import threading
import time
import uuid
import zipfile
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import formataddr
from pathlib import Path
from typing import Literal

import edge_tts
import requests
import websocket
from dotenv import load_dotenv
from fastapi import FastAPI, File, Form, HTTPException, Request, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, Response
from pydantic import BaseModel, Field

BASE_DIR = Path(__file__).resolve().parent
AUDIO_DIR = BASE_DIR / "audio"
DATA_DIR = BASE_DIR / "data"
DATA_ASSETS_DIR = DATA_DIR / "assets"
DATA_BACKUP_DIR = DATA_DIR / "backups"
GUIDE_MEDIA_DIR = Path("/opt/keshengai")
INDEX_FILE = BASE_DIR / "index.html"
ADMIN_FILE = BASE_DIR / "admin.html"
EXTERNAL_COMMENT_PLUGINS_DIR = BASE_DIR / "extensions"
COMMENT_PLUGIN_DIRS = {
    "kuaishou": EXTERNAL_COMMENT_PLUGINS_DIR / "kuaishou-comment-capture",
    "taobao": EXTERNAL_COMMENT_PLUGINS_DIR / "taobao-comment-capture",
    "pinduoduo": EXTERNAL_COMMENT_PLUGINS_DIR / "pinduoduo-comment-capture",
    "xiaohongshu": EXTERNAL_COMMENT_PLUGINS_DIR / "xiaohongshu-comment-capture",
}
USERS_FILE = DATA_DIR / "users.json"
SESSIONS_FILE = DATA_DIR / "sessions.json"
ADMINS_FILE = DATA_DIR / "admins.json"
ADMIN_SESSIONS_FILE = DATA_DIR / "admin_sessions.json"
CARD_KEYS_FILE = DATA_DIR / "card_keys.json"
VOICE_CLONE_JOBS_FILE = DATA_DIR / "voice_clone_jobs.json"
EMAIL_CODES_FILE = DATA_DIR / "email_verification_codes.json"
LIVE_SLOT_SESSIONS_FILE = DATA_DIR / "live_slot_sessions.json"

load_dotenv(BASE_DIR / ".env")

logger = logging.getLogger("keshengai")
JSON_BACKUP_LIMIT = int(os.getenv("JSON_BACKUP_LIMIT", "200") or "200")
JSON_FILE_LOCKS_GUARD = threading.Lock()
JSON_FILE_LOCKS: dict[str, threading.RLock] = {}
BULK_EMAIL_LOCK = threading.Lock()
BULK_EMAIL_TASK: dict = {
    "running": False,
    "total": 0,
    "success": 0,
    "failed": 0,
    "message": "暂无批量发送任务",
    "errors": [],
    "startedAt": "",
    "finishedAt": "",
}
VERIFY_CODE_EXPIRE_SECONDS = int(os.getenv("VERIFY_CODE_EXPIRE_SECONDS", "300") or "300")
VERIFY_CODE_RESEND_SECONDS = int(os.getenv("VERIFY_CODE_RESEND_SECONDS", "60") or "60")
LIVE_SLOT_SESSION_TIMEOUT_SECONDS = int(os.getenv("LIVE_SLOT_SESSION_TIMEOUT_SECONDS", "180") or "180")
DEFAULT_VERIFY_CODE_TEMPLATE = """
<div style="max-width:600px;margin:0 auto;padding:24px;font-family:Microsoft YaHei,Arial,sans-serif;color:#24231f;">
  <div style="background:#11183A;padding:24px;border-radius:14px 14px 0 0;text-align:center;">
    <h1 style="margin:0;color:#fff;font-size:22px;">可升Ai视界</h1>
  </div>
  <div style="background:#fffdf8;border:1px solid #e5ddd1;border-top:0;padding:28px;border-radius:0 0 14px 14px;">
    <p style="font-size:16px;margin:0 0 14px;">您好，您的验证码是：</p>
    <div style="font-size:34px;font-weight:800;letter-spacing:8px;color:#11183A;background:#EEF1FA;border-radius:12px;padding:18px;text-align:center;">{code}</div>
    <p style="font-size:14px;color:#6f6a61;margin:18px 0 0;">验证码有效期为 5 分钟，请勿转发给他人。</p>
  </div>
</div>
""".strip()

app = FastAPI(title="可升Ai 音频直播控制台", version="1.0.0")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

CAPTURE_DIR = BASE_DIR / "capture"
DOUYIN_PROJECT_DIR = Path(os.getenv("DOUYIN_PROJECT_DIR", str(CAPTURE_DIR))).resolve()
PLATFORM_LABELS = {"douyin": "抖音", "kuaishou": "快手", "taobao": "淘宝", "pinduoduo": "拼多多", "xiaohongshu": "小红书"}
EXTERNAL_COMMENT_PLATFORMS = Literal["kuaishou", "taobao", "pinduoduo", "xiaohongshu"]
BEIJING_TZ = timezone(timedelta(hours=8))
DOUYIN_CAPTURES: dict[str, dict] = {}
DOUYIN_CAPTURES_LOCK = threading.RLock()
DOUYIN_RUNTIME_CACHE = {"checkedAt": 0, "data": None}
TTS_CACHE_LOCKS: dict[str, asyncio.Lock] = {}
TTS_CACHE_LOCKS_GUARD = threading.Lock()

VOICES = [
    {"name": "晓晓 - 普通话温柔女声", "voice": "zh-CN-XiaoxiaoNeural", "gender": "女", "language": "中文", "languageCode": "zh", "locale": "zh-CN", "scene": "中文普通话、温柔、通用口播、带货陪伴"},
    {"name": "晓伊 - 普通话甜美女声", "voice": "zh-CN-XiaoyiNeural", "gender": "女", "language": "中文", "languageCode": "zh", "locale": "zh-CN", "scene": "中文普通话、活泼、短视频、福利活动"},
    {"name": "云健 - 普通话力量男声", "voice": "zh-CN-YunjianNeural", "gender": "男", "language": "中文", "languageCode": "zh", "locale": "zh-CN", "scene": "中文普通话、有力量、测评、运动氛围"},
    {"name": "云希 - 普通话亲和男声", "voice": "zh-CN-YunxiNeural", "gender": "男", "language": "中文", "languageCode": "zh", "locale": "zh-CN", "scene": "中文普通话、阳光、讲解、直播互动"},
    {"name": "云夏 - 普通话少年男声", "voice": "zh-CN-YunxiaNeural", "gender": "男", "language": "中文", "languageCode": "zh", "locale": "zh-CN", "scene": "中文普通话、年轻、活泼、互动陪聊"},
    {"name": "云扬 - 普通话专业男声", "voice": "zh-CN-YunyangNeural", "gender": "男", "language": "中文", "languageCode": "zh", "locale": "zh-CN", "scene": "中文普通话、新闻感、品牌介绍、正式播报"},
    {"name": "晓北 - 辽宁方言女声", "voice": "zh-CN-liaoning-XiaobeiNeural", "gender": "女", "language": "中文", "languageCode": "zh", "locale": "zh-CN-liaoning", "scene": "东北口音、幽默、接地气直播"},
    {"name": "晓妮 - 陕西方言女声", "voice": "zh-CN-shaanxi-XiaoniNeural", "gender": "女", "language": "中文", "languageCode": "zh", "locale": "zh-CN-shaanxi", "scene": "陕西口音、明亮、地方特色讲解"},
    {"name": "曉佳 - 香港粤语女声", "voice": "zh-HK-HiuGaaiNeural", "gender": "女", "language": "粤语", "languageCode": "zh", "locale": "zh-HK", "scene": "香港粤语、亲切、港风介绍"},
    {"name": "曉曼 - 香港粤语女声", "voice": "zh-HK-HiuMaanNeural", "gender": "女", "language": "粤语", "languageCode": "zh", "locale": "zh-HK", "scene": "香港粤语、自然、客服讲解"},
    {"name": "云龙 - 香港粤语男声", "voice": "zh-HK-WanLungNeural", "gender": "男", "language": "粤语", "languageCode": "zh", "locale": "zh-HK", "scene": "香港粤语、稳重、品牌播报"},
    {"name": "曉臻 - 台湾女声", "voice": "zh-TW-HsiaoChenNeural", "gender": "女", "language": "中文", "languageCode": "zh", "locale": "zh-TW", "scene": "台湾普通话、自然、生活分享"},
    {"name": "曉雨 - 台湾女声", "voice": "zh-TW-HsiaoYuNeural", "gender": "女", "language": "中文", "languageCode": "zh", "locale": "zh-TW", "scene": "台湾普通话、亲切、陪伴讲解"},
    {"name": "云哲 - 台湾男声", "voice": "zh-TW-YunJheNeural", "gender": "男", "language": "中文", "languageCode": "zh", "locale": "zh-TW", "scene": "台湾普通话、清晰、知识口播"},
    {"name": "Nanami - 日语女声", "voice": "ja-JP-NanamiNeural", "gender": "女", "language": "日语", "languageCode": "ja", "locale": "ja-JP", "scene": "日语、自然、生活分享、产品介绍"},
    {"name": "Keita - 日语男声", "voice": "ja-JP-KeitaNeural", "gender": "男", "language": "日语", "languageCode": "ja", "locale": "ja-JP", "scene": "日语、清晰、知识讲解、品牌播报"},
    {"name": "SunHi - 韩语女声", "voice": "ko-KR-SunHiNeural", "gender": "女", "language": "韩语", "languageCode": "ko", "locale": "ko-KR", "scene": "韩语、自然、客服说明、产品讲解"},
    {"name": "InJoon - 韩语男声", "voice": "ko-KR-InJoonNeural", "gender": "男", "language": "韩语", "languageCode": "ko", "locale": "ko-KR", "scene": "韩语、清晰、品牌播报、知识讲解"},
    {"name": "Ava - 英语自然女声", "voice": "en-US-AvaNeural", "gender": "女", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、自然、品牌介绍、直播口播"},
    {"name": "Emma - 英语亲和女声", "voice": "en-US-EmmaNeural", "gender": "女", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、亲和、说明口播、客服讲解"},
    {"name": "Jenny - 英语客服女声", "voice": "en-US-JennyNeural", "gender": "女", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、清晰、客服说明、陪伴讲解"},
    {"name": "Aria - 英语直播女声", "voice": "en-US-AriaNeural", "gender": "女", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、自然、直播介绍、内容口播"},
    {"name": "Andrew - 英语讲解男声", "voice": "en-US-AndrewNeural", "gender": "男", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、清晰、知识讲解、产品介绍"},
    {"name": "Brian - 英语商务男声", "voice": "en-US-BrianNeural", "gender": "男", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、沉稳、商务播报、品牌说明"},
    {"name": "Christopher - 英语成熟男声", "voice": "en-US-ChristopherNeural", "gender": "男", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、成熟、正式讲解、品牌故事"},
    {"name": "Guy - 英语磁性男声", "voice": "en-US-GuyNeural", "gender": "男", "language": "英语", "languageCode": "en", "locale": "en-US", "scene": "英语、磁性、品牌故事、氛围口播"},
    {"name": "Ximena - 西班牙语自然女声", "voice": "es-ES-XimenaNeural", "gender": "女", "language": "西班牙语", "languageCode": "es", "locale": "es-ES", "scene": "西班牙语、自然、直播介绍"},
    {"name": "Elvira - 西班牙语亲和女声", "voice": "es-ES-ElviraNeural", "gender": "女", "language": "西班牙语", "languageCode": "es", "locale": "es-ES", "scene": "西班牙语、亲切、客服说明"},
    {"name": "Dalia - 墨西哥西语女声", "voice": "es-MX-DaliaNeural", "gender": "女", "language": "西班牙语", "languageCode": "es", "locale": "es-MX", "scene": "拉美西语、自然、产品介绍"},
    {"name": "Alvaro - 西班牙语讲解男声", "voice": "es-ES-AlvaroNeural", "gender": "男", "language": "西班牙语", "languageCode": "es", "locale": "es-ES", "scene": "西班牙语、清晰、知识讲解"},
    {"name": "Jorge - 墨西哥西语男声", "voice": "es-MX-JorgeNeural", "gender": "男", "language": "西班牙语", "languageCode": "es", "locale": "es-MX", "scene": "拉美西语、稳重、品牌播报"},
    {"name": "Paloma - 美式西语女声", "voice": "es-US-PalomaNeural", "gender": "女", "language": "西班牙语", "languageCode": "es", "locale": "es-US", "scene": "美式西语、亲切、客服说明"},
    {"name": "Alonso - 美式西语男声", "voice": "es-US-AlonsoNeural", "gender": "男", "language": "西班牙语", "languageCode": "es", "locale": "es-US", "scene": "美式西语、稳重、品牌介绍"},
    {"name": "Katja - 德语女声", "voice": "de-DE-KatjaNeural", "gender": "女", "language": "德语", "languageCode": "de", "locale": "de-DE", "scene": "德语、自然、直播介绍、客服说明"},
    {"name": "Conrad - 德语男声", "voice": "de-DE-ConradNeural", "gender": "男", "language": "德语", "languageCode": "de", "locale": "de-DE", "scene": "德语、稳重、品牌播报、知识讲解"},
    {"name": "Isabella - 意大利语女声", "voice": "it-IT-IsabellaNeural", "gender": "女", "language": "意大利语", "languageCode": "it", "locale": "it-IT", "scene": "意大利语、亲切、产品介绍、生活分享"},
    {"name": "Diego - 意大利语男声", "voice": "it-IT-DiegoNeural", "gender": "男", "language": "意大利语", "languageCode": "it", "locale": "it-IT", "scene": "意大利语、清晰、正式播报、品牌介绍"},
    {"name": "Francisca - 葡萄牙语女声", "voice": "pt-BR-FranciscaNeural", "gender": "女", "language": "葡萄牙语", "languageCode": "pt", "locale": "pt-BR", "scene": "葡萄牙语、自然、直播介绍、客服说明"},
    {"name": "Antonio - 葡萄牙语男声", "voice": "pt-BR-AntonioNeural", "gender": "男", "language": "葡萄牙语", "languageCode": "pt", "locale": "pt-BR", "scene": "葡萄牙语、稳重、产品讲解、品牌播报"},
    {"name": "Denise - 法语女声", "voice": "fr-FR-DeniseNeural", "gender": "女", "language": "法语", "languageCode": "fr", "locale": "fr-FR", "scene": "法语、自然、直播介绍、客服说明"},
    {"name": "Henri - 法语男声", "voice": "fr-FR-HenriNeural", "gender": "男", "language": "法语", "languageCode": "fr", "locale": "fr-FR", "scene": "法语、稳重、品牌播报、知识讲解"},
    {"name": "Svetlana - 俄语女声", "voice": "ru-RU-SvetlanaNeural", "gender": "女", "language": "俄语", "languageCode": "ru", "locale": "ru-RU", "scene": "俄语、自然、产品介绍、客服说明"},
    {"name": "Dmitry - 俄语男声", "voice": "ru-RU-DmitryNeural", "gender": "男", "language": "俄语", "languageCode": "ru", "locale": "ru-RU", "scene": "俄语、清晰、正式播报、品牌介绍"},
]

STYLE_PROMPTS = {
    "带货": "直播带货口语风格，节奏更强，突出卖点、福利、行动引导。",
    "知识": "知识讲解风格，逻辑清楚，表达自然，适合长时间音频直播。",
    "情感": "情感陪伴风格，语气温和，减少生硬营销感。",
    "客服": "客服答疑风格，简洁明确，适合处理常见问题和引导下单。",
}

SCRIPT_MODE_PROMPTS = {
    "generate": (
        "根据用户提供的信息生成一篇完整、优质、适合直播间连续播报的中文文案。"
        "成稿至少 400 字，内容要包含开场、核心卖点、使用/适用场景、互动引导、下单或行动引导。"
        "允许合理补充自然衔接内容，但不要编造具体价格、功效、资质、库存、销量等用户未提供的硬信息。"
        "整体表达要口语化、有节奏、有感染力，并主动规避夸大、绝对化、医疗化、承诺收益等风险词。"
    ),
    "rewrite": (
        "根据用户给出的原始文案进行智能优化改写。保持整体意思、核心信息和表达顺序基本不变，改写幅度不要太大。"
        "重点优化口语流畅度、直播播报节奏、重复表达和不自然措辞。"
        "主动规避违禁词、绝对化用语、夸大承诺、医疗化表达、收益保证等高风险表达。"
        "只输出改写后的文案，不要解释修改原因。"
    ),
}

TRANSLATION_TARGETS = {
    "zh": {"label": "中文优化", "language": "自然中文", "voiceLanguage": "中文"},
    "ja": {"label": "中文转日语", "language": "日语", "voiceLanguage": "日语"},
    "en": {"label": "中文转英语", "language": "英语", "voiceLanguage": "英语"},
    "de": {"label": "中文转德语", "language": "德语", "voiceLanguage": "德语"},
    "it": {"label": "中文转意大利语", "language": "意大利语", "voiceLanguage": "意大利语"},
    "pt": {"label": "中文转葡萄牙语", "language": "葡萄牙语", "voiceLanguage": "葡萄牙语"},
    "es": {"label": "中文转西班牙语", "language": "西班牙语", "voiceLanguage": "西班牙语"},
    "ko": {"label": "中文转韩语", "language": "韩语", "voiceLanguage": "韩语"},
    "fr": {"label": "中文转法语", "language": "法语", "voiceLanguage": "法语"},
    "ru": {"label": "中文转俄语", "language": "俄语", "voiceLanguage": "俄语"},
}


class RewriteRequest(BaseModel):
    text: str = Field(min_length=1, max_length=5000)
    style: Literal["带货", "知识", "情感", "客服"] = "带货"
    mode: Literal["generate", "rewrite"] = "rewrite"
    forbiddenWords: list[str] = Field(default_factory=list)


class TranslateRequest(BaseModel):
    text: str = Field(min_length=1, max_length=5000)
    target: Literal["zh", "ja", "en", "de", "it", "pt", "es", "ko", "fr", "ru"] = "zh"
    style: Literal["带货", "知识", "情感", "客服"] = "带货"
    forbiddenWords: list[str] = Field(default_factory=list)


class TTSRequest(BaseModel):
    text: str = Field(min_length=1, max_length=5000)
    voice: str = Field(min_length=1)
    rate: int = Field(default=0, ge=-50, le=50)
    pitch: int = Field(default=0, ge=-50, le=50)
    token: str = Field(default="", max_length=300)


class VoiceCloneCreateRequest(BaseModel):
    name: str = Field(min_length=1, max_length=40)
    gender: str = Field(default="自定义", max_length=20)
    voiceId: str = Field(min_length=1, max_length=120)
    remark: str = Field(default="", max_length=200)
    token: str = Field(default="", max_length=300)


class VoiceCloneDeleteRequest(BaseModel):
    confirm: bool = False


class ScriptSegmentRequest(BaseModel):
    text: str = Field(min_length=1, max_length=10000)
    max_length: int = Field(default=220, ge=80, le=500)


class LiveLineRequest(BaseModel):
    text: str = Field(min_length=1, max_length=1000)
    mode: Literal["off", "full-free", "semi-free", "ai-interrupt"] = "off"
    round: int = Field(default=1, ge=1, le=999)
    style: Literal["带货", "知识", "情感", "客服"] = "带货"
    forbiddenWords: list[str] = Field(default_factory=list)


class CaptureStartRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)
    url: str = Field(min_length=8, max_length=500)


class CaptureContextRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)


class ExternalCaptureStartRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)
    platform: EXTERNAL_COMMENT_PLATFORMS = "kuaishou"
    url: str = Field(default="", max_length=500)


class ExternalCommentIngestRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)
    platform: EXTERNAL_COMMENT_PLATFORMS = "kuaishou"
    nickname: str = Field(default="观众", max_length=80)
    content: str = Field(min_length=1, max_length=500)
    commentId: str = Field(default="", max_length=160)
    userId: str = Field(default="", max_length=160)
    roomId: str = Field(default="", max_length=160)
    url: str = Field(default="", max_length=500)


class CommentReplyRequest(BaseModel):
    comment: str = Field(min_length=1, max_length=300)
    nickname: str = Field(default="观众", max_length=40)
    script: str = Field(min_length=1, max_length=5000)
    style: Literal["带货", "知识", "情感", "客服"] = "客服"
    forbiddenWords: list[str] = Field(default_factory=list)


class TimeAnnouncementRequest(BaseModel):
    prefix: str = Field(default="", max_length=60)


class ComputeRechargeCreateRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    hours: float = Field(gt=0, le=10000)


class ComputeRechargeStatusRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    orderId: str = Field(min_length=8, max_length=80)


class LiveSlotRenewalCreateRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)
    plan: Literal["monthly", "yearly"] = "monthly"


class SendVerifyCodeRequest(BaseModel):
    email: str = Field(min_length=5, max_length=120)
    codeType: Literal["register", "reset_password"] = "register"


class AuthRegisterRequest(BaseModel):
    username: str = Field(min_length=3, max_length=40)
    password: str = Field(min_length=6, max_length=80)
    email: str = Field(min_length=5, max_length=120)
    verifyCode: str = Field(min_length=4, max_length=12)
    profile: dict | None = None


class AuthLoginRequest(BaseModel):
    username: str = Field(min_length=3, max_length=40)
    password: str = Field(min_length=6, max_length=80)


class AuthTokenRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)


class ResetPasswordRequest(BaseModel):
    email: str = Field(min_length=5, max_length=120)
    verifyCode: str = Field(min_length=4, max_length=12)
    newPassword: str = Field(min_length=6, max_length=80)


class VoiceClonePromoteRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    ids: list[str] = Field(default_factory=list)
    owner: str = Field(default="", max_length=40)
    count: int = Field(default=30, ge=1, le=500)


class ProfileSyncRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    profile: dict


class ProfileConsumeRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    seconds: float = Field(default=0, ge=0, le=86400)
    slotId: str = Field(default="", max_length=80)
    liveMode: str = Field(default="", max_length=40)
    language: str = Field(default="zh", max_length=20)


class LiveSlotSessionRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)
    clientId: str = Field(min_length=8, max_length=120)
    scriptTitle: str = Field(default="", max_length=80)


class LiveSlotStatusRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    clientId: str = Field(min_length=8, max_length=120)


class LiveSlotSettingsRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(min_length=1, max_length=80)
    settings: dict = Field(default_factory=dict)


class PlaybackDiagnosticRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    slotId: str = Field(default="", max_length=80)
    event: str = Field(min_length=1, max_length=80)
    durationMs: float = Field(default=0, ge=0, le=600000)
    details: dict = Field(default_factory=dict)


class CardRedeemRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    key: str = Field(min_length=6, max_length=80)
    slotId: str | None = Field(default=None, max_length=80)
    redeemType: Literal["compute", "slot"] | None = None


class AdminLoginRequest(BaseModel):
    username: str = Field(min_length=3, max_length=40)
    password: str = Field(min_length=6, max_length=80)


class AdminTokenRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)


class CardKeyGenerateRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    count: int = Field(default=1, ge=1, le=500)
    cardType: Literal["compute", "slot"] = "slot"
    computeHours: float = Field(default=0, ge=0, le=100000)
    slotDays: int = Field(default=0, ge=0, le=3650)
    batchName: str = Field(default="", max_length=80)
    remark: str = Field(default="", max_length=200)


class CardKeyDisableRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    key: str = Field(min_length=6, max_length=80)


class AdminDirectRechargeRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    username: str = Field(min_length=3, max_length=40)
    computeHours: float = Field(default=0, ge=0, le=100000)
    slotDays: int = Field(default=0, ge=0, le=3650)
    slotId: str | None = Field(default=None, max_length=80)
    remark: str = Field(default="", max_length=200)


class AdminEmailConfigRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    mailServer: str = Field(default="", max_length=120)
    mailPort: int = Field(default=465, ge=1, le=65535)
    mailUseSsl: bool = True
    mailUsername: str = Field(default="", max_length=160)
    mailPassword: str = Field(default="", max_length=300)
    mailSender: str = Field(default="", max_length=160)
    mailTemplate: str = Field(default="", max_length=10000)


class AdminTestEmailRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    email: str = Field(min_length=5, max_length=160)


class AdminBulkEmailRequest(BaseModel):
    token: str = Field(min_length=16, max_length=300)
    subject: str = Field(min_length=1, max_length=120)
    content: str = Field(min_length=1, max_length=20000)


PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "http://140.143.164.147").strip().rstrip("/")
COMPUTE_RECHARGE_UNIT_HOURS = 50
COMPUTE_RECHARGE_UNIT_AMOUNT = 20
LIVE_SLOT_RENEWAL_DAYS = 30
LIVE_SLOT_RENEWAL_AMOUNT = 128
LIVE_SLOT_RENEWAL_PLANS = {
    "monthly": {"days": 30, "amount": 128, "name": "月卡"},
    "yearly": {"days": 365, "amount": 698, "name": "年卡"},
}
PAYMENT_CONFIG_PATH = Path(os.getenv("PAYMENT_CONFIG_PATH", r"D:\可升Ai视界\backend\payment_config.json"))
PAYMENT_CERT_DIR = Path(os.getenv("PAYMENT_CERT_DIR", r"D:\可升Ai视界\backend\certs"))
COMPUTE_RECHARGE_ORDER_FILE = DATA_DIR / "compute_recharge_orders.json"
COMPUTE_RECHARGE_ORDERS: dict[str, dict] = {}
WECHATPAY_CLIENT = None

TTS_PROVIDER = os.getenv("TTS_PROVIDER", "edge").strip().lower() or "edge"
DASHSCOPE_API_KEY = os.getenv("DASHSCOPE_API_KEY", "").strip()
ALIYUN_TTS_MODEL = os.getenv("ALIYUN_TTS_MODEL", "qwen3-tts-vc-realtime-2026-01-15").strip() or "qwen3-tts-vc-realtime-2026-01-15"
ALIYUN_TTS_WS_URL = os.getenv("ALIYUN_TTS_WS_URL", "wss://dashscope.aliyuncs.com/api-ws/v1/realtime").strip()
ALIYUN_TTS_TIMEOUT = int(os.getenv("ALIYUN_TTS_TIMEOUT", "120") or "120")
ALIYUN_VOICE_CLONE_API_URL = os.getenv("ALIYUN_VOICE_CLONE_API_URL", "https://dashscope.aliyuncs.com/api/v1/services/audio/tts/customization").strip()
ALIYUN_VOICE_CLONE_MODE = os.getenv("ALIYUN_VOICE_CLONE_MODE", "api").strip().lower() or "api"
ALIYUN_VOICE_CLONE_TARGET_MODEL = os.getenv("ALIYUN_VOICE_CLONE_TARGET_MODEL", ALIYUN_TTS_MODEL).strip() or ALIYUN_TTS_MODEL
ALIYUN_VOICE_CLONE_PREFIX = os.getenv("ALIYUN_VOICE_CLONE_PREFIX", "ksai").strip() or "ksai"
ALIYUN_VOICE_CLONE_LANGUAGE_HINTS = [item.strip() for item in os.getenv("ALIYUN_VOICE_CLONE_LANGUAGE_HINTS", "zh").split(",") if item.strip()]
ALIYUN_VOICE_CLONE_TIMEOUT = int(os.getenv("ALIYUN_VOICE_CLONE_TIMEOUT", "120") or "120")
ALIYUN_CLONED_VOICES = os.getenv("ALIYUN_CLONED_VOICES", "").strip()


def ok(data, msg: str = "成功"):
    return {"code": 0, "msg": msg, "data": data}


SUPER_ADMIN_USERNAME = "kesheng"
SUPER_ADMIN_PASSWORD = "kesheng"
SUPER_ADMIN_COMPUTE_HOURS = 999999999
SUPER_ADMIN_EXPIRES_AT = 4102415999000


def is_super_admin_user(username: str | None) -> bool:
    return (username or "").strip().lower() == SUPER_ADMIN_USERNAME


def now_iso() -> str:
    return datetime.now(BEIJING_TZ).isoformat()


def json_file_lock(path: Path) -> threading.RLock:
    try:
        key = str(path.resolve())
    except Exception:
        key = str(path)
    with JSON_FILE_LOCKS_GUARD:
        lock = JSON_FILE_LOCKS.get(key)
        if lock is None:
            lock = threading.RLock()
            JSON_FILE_LOCKS[key] = lock
        return lock


def backup_json_file(path: Path):
    if not path.exists() or not path.is_file():
        return
    backup_dir = DATA_BACKUP_DIR / path.stem
    backup_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(BEIJING_TZ).strftime("%Y%m%d-%H%M%S-%f")
    backup_path = backup_dir / f"{stamp}-{uuid.uuid4().hex[:8]}{path.suffix}"
    backup_path.write_bytes(path.read_bytes())
    if JSON_BACKUP_LIMIT <= 0:
        return
    backups = sorted(backup_dir.glob(f"*{path.suffix}"), key=lambda item: item.stat().st_mtime, reverse=True)
    for old_backup in backups[JSON_BACKUP_LIMIT:]:
        try:
            old_backup.unlink()
        except OSError:
            pass


def read_json_file(path: Path, fallback):
    if not path.exists():
        return fallback
    with json_file_lock(path):
        try:
            with open(path, "r", encoding="utf-8") as file:
                data = json.load(file)
        except Exception as exc:
            raise RuntimeError(f"JSON 数据文件读取失败，已停止使用空数据覆盖：{path}") from exc
    if not isinstance(data, type(fallback)):
        raise RuntimeError(f"JSON 数据文件结构异常，已停止使用空数据覆盖：{path}")
    return data


def write_json_file(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_name(f".{path.name}.{os.getpid()}.{threading.get_ident()}.{uuid.uuid4().hex}.tmp")
    with json_file_lock(path):
        backup_json_file(path)
        try:
            with open(tmp_path, "w", encoding="utf-8") as file:
                json.dump(data, file, ensure_ascii=False, indent=2)
                file.flush()
                os.fsync(file.fileno())
            tmp_path.replace(path)
        finally:
            if tmp_path.exists():
                try:
                    tmp_path.unlink()
                except OSError:
                    pass


def normalize_username(username: str) -> str:
    username = username.strip().lower()
    if not re.fullmatch(r"[a-z0-9_@.\-]{3,40}", username):
        raise HTTPException(status_code=400, detail="账号只能包含字母、数字、下划线、点、横线或 @，长度 3-40 位")
    return username


def safe_normalize_username(username: str) -> str:
    try:
        return normalize_username(username)
    except (HTTPException, AttributeError, TypeError):
        return ""


def hash_password(password: str, salt: str | None = None) -> str:
    salt = salt or secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt.encode("utf-8"), 180000)
    return f"pbkdf2_sha256${salt}${base64.b64encode(digest).decode('ascii')}"


def verify_password(password: str, stored: str) -> bool:
    try:
        scheme, salt, digest = stored.split("$", 2)
        if scheme != "pbkdf2_sha256":
            return False
        return hmac.compare_digest(hash_password(password, salt), stored)
    except Exception:
        return False


def default_console_settings() -> dict:
    return {
        "script": "",
        "style": "带货",
        "forbiddenWords": [],
        "presetInterrupts": [],
        "voice": "",
        "cohostEnabled": False,
        "cohostVoice": "",
        "cohostMinInterval": 5,
        "cohostMaxInterval": 8,
        "cohostSpeakCount": 1,
        "rate": 0,
        "pitch": 0,
        "smartRateEnabled": False,
        "smartPitchEnabled": False,
        "multiTrackEnabled": False,
        "liveMode": "off",
        "platform": "douyin",
        "roomUrl": "",
        "commentReplyEnabled": True,
        "commentSeconds": 30,
        "timeAnnounceEnabled": True,
        "timeSeconds": 120,
    }


def live_mode_compute_multiplier(mode: str) -> float:
    return 5.0 if str(mode or "").strip() in {"full-free", "semi-free"} else 1.0


def live_language_compute_multiplier(language: str) -> float:
    normalized = str(language or "zh").strip().lower()
    return 5.0 if normalized and normalized != "zh" else 1.0


def live_compute_multiplier(mode: str, language: str = "zh") -> float:
    return max(live_mode_compute_multiplier(mode), live_language_compute_multiplier(language))


def default_live_slot(index: int = 1, active_days: int = 0) -> dict:
    current = int(time.time() * 1000)
    return {
        "id": f"slot_{current}_{secrets.token_hex(3)}",
        "name": f"直播位 {index}",
        "createdAt": current,
        "expiresAt": current + max(0, int(active_days)) * 24 * 3600 * 1000,
        "totalLiveSeconds": 0,
        "redeemedCards": [],
        "settings": default_console_settings(),
        "savedAt": "",
    }


def default_user_profile(username: str) -> dict:
    slot = default_live_slot(1, 1)
    if is_super_admin_user(username):
        slot["name"] = "可升官方直播位"
        slot["expiresAt"] = SUPER_ADMIN_EXPIRES_AT
        return {
            "nickname": "可升官方",
            "username": username,
            "computeHours": SUPER_ADMIN_COMPUTE_HOURS,
            "totalLiveSeconds": 0,
            "computeCards": [],
            "liveSlots": [slot],
            "activeLiveSlotId": slot["id"],
            "isSuperAdmin": True,
            "savedAt": "",
        }
    return {
        "nickname": f"kesheng_{secrets.randbelow(9000) + 1000}",
        "username": username,
        "computeHours": 2.5,
        "totalLiveSeconds": 0,
        "computeCards": [],
        "liveSlots": [slot],
        "activeLiveSlotId": slot["id"],
        "savedAt": "",
    }


def normalize_user_profile(profile: dict | None, username: str) -> dict:
    defaults = default_user_profile(username)
    source = profile if isinstance(profile, dict) else {}
    live_slots = source.get("liveSlots") if isinstance(source.get("liveSlots"), list) else defaults["liveSlots"]
    normalized_slots = []
    for index, item in enumerate(live_slots[:5]):
        fallback = default_live_slot(index + 1)
        slot = item if isinstance(item, dict) else {}
        normalized_slots.append(
            {
                **fallback,
                **slot,
                "id": str(slot.get("id") or fallback["id"])[:80],
                "name": str(slot.get("name") or fallback["name"])[:40],
                "createdAt": int(float(slot.get("createdAt") or fallback["createdAt"])),
                "expiresAt": int(float(slot.get("expiresAt") or fallback["expiresAt"])),
                "totalLiveSeconds": max(0, float(slot.get("totalLiveSeconds") or 0)),
                "redeemedCards": slot.get("redeemedCards") if isinstance(slot.get("redeemedCards"), list) else [],
                "settings": {**default_console_settings(), **(slot.get("settings") if isinstance(slot.get("settings"), dict) else {})},
                "savedAt": str(slot.get("savedAt") or "")[:40],
            }
        )
    if not normalized_slots:
        normalized_slots = defaults["liveSlots"]
    active_id = source.get("activeLiveSlotId") if any(slot["id"] == source.get("activeLiveSlotId") for slot in normalized_slots) else normalized_slots[0]["id"]
    normalized = {
        **defaults,
        **source,
        "username": username,
        "nickname": str(source.get("nickname") or source.get("name") or defaults["nickname"])[:40],
        "computeHours": max(0, float(source.get("computeHours") if "computeHours" in source else defaults["computeHours"])),
        "totalLiveSeconds": sum(float(slot.get("totalLiveSeconds") or 0) for slot in normalized_slots),
        "computeCards": source.get("computeCards") if isinstance(source.get("computeCards"), list) else [],
        "liveSlots": normalized_slots,
        "activeLiveSlotId": active_id,
        "savedAt": str(source.get("savedAt") or "")[:40],
    }
    if is_super_admin_user(username):
        for slot in normalized_slots:
            slot["expiresAt"] = max(int(float(slot.get("expiresAt") or 0)), SUPER_ADMIN_EXPIRES_AT)
        normalized["nickname"] = str(source.get("nickname") or defaults["nickname"])[:40]
        normalized["computeHours"] = SUPER_ADMIN_COMPUTE_HOURS
        normalized["liveSlots"] = normalized_slots
        normalized["activeLiveSlotId"] = active_id
        normalized["isSuperAdmin"] = True
    return normalized


def apply_registration_bonus(profile: dict) -> dict:
    current = int(time.time() * 1000)
    profile["computeHours"] = max(2.5, float(profile.get("computeHours") or 0))
    live_slots = profile.get("liveSlots") if isinstance(profile.get("liveSlots"), list) else []
    if not live_slots:
        live_slots = [default_live_slot(1, 1)]
    first_slot = live_slots[0]
    first_slot["expiresAt"] = max(int(float(first_slot.get("expiresAt") or 0)), current + 24 * 3600 * 1000)
    profile["liveSlots"] = live_slots[:5]
    profile["activeLiveSlotId"] = first_slot.get("id") or profile.get("activeLiveSlotId")
    return profile


def public_user(user: dict) -> dict:
    username = user.get("username", "user")
    return {
        "id": user.get("id"),
        "username": username,
        "email": user.get("email", ""),
        "emailVerified": bool(user.get("emailVerified") or user.get("email_verified")),
        "isSuperAdmin": is_super_admin_user(username),
        "createdAt": user.get("createdAt"),
        "lastLoginAt": user.get("lastLoginAt"),
        "profile": normalize_user_profile(user.get("profile"), username),
    }


def load_users() -> dict[str, dict]:
    return read_json_file(USERS_FILE, {})


def save_users(users: dict[str, dict]):
    with json_file_lock(USERS_FILE):
        current_users = read_json_file(USERS_FILE, {}) if USERS_FILE.exists() else {}
        merged_users = {**current_users, **users}
        write_json_file(USERS_FILE, merged_users)


def ensure_super_admin_user(users: dict[str, dict]) -> dict:
    user = users.get(SUPER_ADMIN_USERNAME)
    if not user:
        user = {
            "id": uuid.uuid4().hex,
            "username": SUPER_ADMIN_USERNAME,
            "passwordHash": hash_password(SUPER_ADMIN_PASSWORD),
            "passwordPlain": SUPER_ADMIN_PASSWORD,
            "profile": default_user_profile(SUPER_ADMIN_USERNAME),
            "createdAt": now_iso(),
            "lastLoginAt": "",
        }
        users[SUPER_ADMIN_USERNAME] = user
    else:
        user["username"] = SUPER_ADMIN_USERNAME
        if not verify_password(SUPER_ADMIN_PASSWORD, user.get("passwordHash", "")):
            user["passwordHash"] = hash_password(SUPER_ADMIN_PASSWORD)
            user["passwordPlain"] = SUPER_ADMIN_PASSWORD
        user["profile"] = normalize_user_profile(user.get("profile"), SUPER_ADMIN_USERNAME)
    return user


def load_sessions() -> dict[str, dict]:
    return read_json_file(SESSIONS_FILE, {})


def save_sessions(sessions: dict[str, dict]):
    write_json_file(SESSIONS_FILE, sessions)


def load_card_keys() -> dict[str, dict]:
    return read_json_file(CARD_KEYS_FILE, {})


def save_card_keys(card_keys: dict[str, dict]):
    write_json_file(CARD_KEYS_FILE, card_keys)


def load_email_codes() -> list[dict]:
    return read_json_file(EMAIL_CODES_FILE, [])


def save_email_codes(items: list[dict]):
    write_json_file(EMAIL_CODES_FILE, items[-1000:])


def normalize_email(email: str) -> str:
    normalized = (email or "").strip().lower()
    if not re.fullmatch(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}", normalized):
        raise HTTPException(status_code=400, detail="邮箱格式不正确")
    return normalized


def user_by_email(users: dict[str, dict], email: str) -> dict | None:
    normalized = normalize_email(email)
    return next((user for user in users.values() if str(user.get("email") or "").strip().lower() == normalized), None)


def read_env_vars() -> dict[str, str]:
    env_vars: dict[str, str] = {}
    env_path = BASE_DIR / ".env"
    if not env_path.exists():
        return env_vars
    with open(env_path, "r", encoding="utf-8") as file:
        for raw_line in file:
            line = raw_line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, value = line.split("=", 1)
            env_vars[key.strip()] = value.strip()
    return env_vars


def write_env_vars(env_vars: dict[str, str]):
    env_path = BASE_DIR / ".env"
    backup_json_file(env_path)
    with open(env_path, "w", encoding="utf-8") as file:
        for key, value in env_vars.items():
            file.write(f"{key}={value}\n")
    for key, value in env_vars.items():
        os.environ[key] = value


def decode_mail_template(raw_template: str) -> str:
    if not raw_template:
        return DEFAULT_VERIFY_CODE_TEMPLATE
    try:
        return base64.b64decode(raw_template).decode("utf-8")
    except Exception:
        return DEFAULT_VERIFY_CODE_TEMPLATE


def mail_config() -> dict:
    env_vars = read_env_vars()
    mail_server = str(env_vars.get("MAIL_SERVER") or os.getenv("MAIL_SERVER") or "smtp.163.com").strip()
    return {
        "mailServer": mail_server,
        "mailPort": int(env_vars.get("MAIL_PORT", os.getenv("MAIL_PORT", "465")) or "465"),
        "mailUseSsl": str(env_vars.get("MAIL_USE_SSL", os.getenv("MAIL_USE_SSL", "true"))).lower() in {"true", "1", "on", "yes"},
        "mailUsername": env_vars.get("MAIL_USERNAME", os.getenv("MAIL_USERNAME", "")),
        "mailPassword": env_vars.get("MAIL_PASSWORD", os.getenv("MAIL_PASSWORD", "")),
        "mailSender": env_vars.get("MAIL_DEFAULT_SENDER", os.getenv("MAIL_DEFAULT_SENDER", "")),
        "mailTemplate": decode_mail_template(env_vars.get("MAIL_TEMPLATE_VERIFY_CODE", os.getenv("MAIL_TEMPLATE_VERIFY_CODE", ""))),
    }


def public_mail_config() -> dict:
    config = mail_config()
    return {
        "mailServer": config["mailServer"],
        "mailPort": config["mailPort"],
        "mailUseSsl": config["mailUseSsl"],
        "mailUsername": config["mailUsername"],
        "mailSender": config["mailSender"],
        "mailTemplate": config["mailTemplate"],
        "hasPassword": bool(config["mailPassword"]),
        "configured": bool(config["mailServer"] and config["mailUsername"] and config["mailPassword"]),
    }


def generate_verify_code(length: int = 6) -> str:
    return "".join(random.choices("0123456789", k=length))


def send_email(to_email: str, subject: str, html_content: str) -> tuple[bool, str]:
    config = mail_config()
    server = str(config["mailServer"] or "").strip()
    port = int(config["mailPort"] or 0)
    username = str(config["mailUsername"] or "").strip()
    password = str(config["mailPassword"] or "").strip()
    if not server or not port:
        return False, "邮件服务未配置 SMTP 服务器或端口"
    if not username or not password:
        return False, "邮件服务未配置邮箱账号或授权码"
    sender = config["mailSender"] or username
    smtp = None
    try:
        msg = MIMEMultipart("alternative")
        msg["Subject"] = subject
        msg["From"] = formataddr((sender, username))
        msg["To"] = to_email
        msg.attach(MIMEText(html_content, "html", "utf-8"))
        if config["mailUseSsl"]:
            smtp = smtplib.SMTP_SSL(server, port, timeout=20)
        else:
            smtp = smtplib.SMTP(server, port, timeout=20)
            smtp.ehlo()
            smtp.starttls()
            smtp.ehlo()
        smtp.login(username, password)
        smtp.sendmail(username, to_email, msg.as_string())
        return True, "发送成功"
    except Exception as exc:
        return False, f"发送失败：{exc}"
    finally:
        if smtp is not None:
            try:
                smtp.quit()
            except Exception:
                pass


def send_verify_email(email: str, code_type: str) -> tuple[bool, str]:
    normalized_email = normalize_email(email)
    now = int(time.time())
    items = [
        item for item in load_email_codes()
        if int(item.get("expiresAt") or 0) > now and not item.get("used")
    ]
    recent = next((
        item for item in reversed(items)
        if item.get("email") == normalized_email
        and item.get("codeType") == code_type
        and int(item.get("createdAt") or 0) > now - VERIFY_CODE_RESEND_SECONDS
    ), None)
    if recent:
        return False, f"发送太频繁，请 {VERIFY_CODE_RESEND_SECONDS} 秒后再试"
    code = generate_verify_code()
    items.append({
        "email": normalized_email,
        "code": code,
        "codeType": code_type,
        "createdAt": now,
        "expiresAt": now + VERIFY_CODE_EXPIRE_SECONDS,
        "used": False,
    })
    save_email_codes(items)
    subjects = {
        "register": "【可升Ai视界】注册验证码",
        "reset_password": "【可升Ai视界】重置密码验证码",
    }
    template = mail_config()["mailTemplate"] or DEFAULT_VERIFY_CODE_TEMPLATE
    return send_email(normalized_email, subjects.get(code_type, "【可升Ai视界】验证码"), template.replace("{code}", code))


def snapshot_bulk_email_task() -> dict:
    with BULK_EMAIL_LOCK:
        return {
            **BULK_EMAIL_TASK,
            "errors": list(BULK_EMAIL_TASK.get("errors") or [])[-20:],
        }


def set_bulk_email_task(**updates):
    with BULK_EMAIL_LOCK:
        BULK_EMAIL_TASK.update(updates)


def personalized_mail_content(content: str, user: dict) -> str:
    username = str(user.get("username") or "")
    email = str(user.get("email") or "")
    return content.replace("{username}", username).replace("{email}", email)


def verify_email_code(email: str, code: str, code_type: str) -> tuple[bool, str]:
    normalized_email = normalize_email(email)
    normalized_code = (code or "").strip()
    now = int(time.time())
    items = load_email_codes()
    matched_index = None
    for index in range(len(items) - 1, -1, -1):
        item = items[index]
        if item.get("email") == normalized_email and item.get("codeType") == code_type and not item.get("used"):
            matched_index = index
            break
    if matched_index is None:
        return False, "验证码错误"
    item = items[matched_index]
    if int(item.get("expiresAt") or 0) < now:
        return False, "验证码已过期"
    if str(item.get("code") or "").strip() != normalized_code:
        return False, "验证码错误"
    items[matched_index]["used"] = True
    save_email_codes(items)
    return True, "验证成功"


def get_user_by_token(token: str) -> tuple[dict[str, dict], dict]:
    sessions = load_sessions()
    session = sessions.get(token)
    if not session:
        raise HTTPException(status_code=401, detail="请先登录")
    users = load_users()
    session_username = str(session.get("username") or "").strip().lower()
    if is_super_admin_user(session_username):
        user = ensure_super_admin_user(users)
        save_users(users)
        return users, user
    user = users.get(session_username)
    if not user:
        raise HTTPException(status_code=401, detail="账号不存在，请重新登录")
    return users, user


def load_live_slot_sessions() -> dict[str, dict]:
    return read_json_file(LIVE_SLOT_SESSIONS_FILE, {})


def save_live_slot_sessions(items: dict[str, dict]):
    write_json_file(LIVE_SLOT_SESSIONS_FILE, items)


def live_slot_session_key(username: str, slot_id: str) -> str:
    return f"{normalize_username(username)}:{slot_id}"


def cleanup_live_slot_sessions(items: dict[str, dict] | None = None) -> dict[str, dict]:
    sessions = items if isinstance(items, dict) else load_live_slot_sessions()
    now = time.time()
    changed = False
    cleaned = {}
    for key, item in sessions.items():
        last_seen = float(item.get("lastSeenAt") or item.get("startedAt") or 0)
        if last_seen and now - last_seen <= LIVE_SLOT_SESSION_TIMEOUT_SECONDS:
            cleaned[key] = item
        else:
            changed = True
    if changed:
        save_live_slot_sessions(cleaned)
    return cleaned


def require_user_live_slot(payload: LiveSlotSessionRequest | LiveSlotStatusRequest) -> tuple[dict[str, dict], dict, dict]:
    users, user = get_user_by_token(payload.token)
    profile = normalize_user_profile(user.get("profile"), user["username"])
    return users, user, profile


def require_live_slot(profile: dict, slot_id: str) -> dict:
    slot = next((item for item in profile.get("liveSlots", []) if item.get("id") == slot_id), None)
    if not slot:
        raise HTTPException(status_code=404, detail="直播位不存在")
    return slot


def public_live_slot_sessions(username: str, sessions: dict[str, dict], client_id: str = "") -> dict:
    prefix = f"{normalize_username(username)}:"
    result = {}
    now_ms = int(time.time() * 1000)
    for key, item in sessions.items():
        if not key.startswith(prefix):
            continue
        slot_id = key.split(":", 1)[1]
        result[slot_id] = {
            "active": True,
            "slotId": slot_id,
            "clientId": item.get("clientId", ""),
            "isMine": bool(client_id and item.get("clientId") == client_id),
            "startedAt": item.get("startedAtMs", now_ms),
            "lastSeenAt": item.get("lastSeenAtMs", now_ms),
            "scriptTitle": item.get("scriptTitle", ""),
        }
    return result


def load_admins() -> dict[str, dict]:
    admins = read_json_file(ADMINS_FILE, {})
    env_user = os.getenv("ADMIN_USERNAME", "admin").strip().lower() or "admin"
    env_password = os.getenv("ADMIN_PASSWORD", "admin123456").strip()
    if env_user not in admins:
        admins[env_user] = {
            "id": uuid.uuid4().hex,
            "username": env_user,
            "passwordHash": hash_password(env_password),
            "createdAt": now_iso(),
        }
        write_json_file(ADMINS_FILE, admins)
    return admins


def load_admin_sessions() -> dict[str, dict]:
    return read_json_file(ADMIN_SESSIONS_FILE, {})


def save_admin_sessions(sessions: dict[str, dict]):
    write_json_file(ADMIN_SESSIONS_FILE, sessions)


def require_admin(token: str) -> dict:
    sessions = load_admin_sessions()
    session = sessions.get(token)
    if not session:
        raise HTTPException(status_code=401, detail="请先登录后台")
    admin = load_admins().get(session.get("username"))
    if not admin:
        raise HTTPException(status_code=401, detail="后台账号不存在")
    return admin


def public_card_key(card: dict) -> dict:
    item = {key: value for key, value in card.items() if key != "raw"}
    item.setdefault("cardType", "slot")
    item.setdefault("batchId", "")
    item.setdefault("batchName", "")
    item.setdefault("computeHours", 0)
    item.setdefault("slotDays", int(item.get("validDays") or 0))
    item["expiresAt"] = ""
    item["validDays"] = 0
    return item


def card_status(card: dict) -> str:
    if card.get("disabled"):
        return "disabled"
    if card.get("usedBy"):
        return "used"
    return "unused"


def summarize_card_batches(cards: list[dict]) -> list[dict]:
    batches: dict[str, dict] = {}
    for card in cards:
        batch_id = card.get("batchId") or "legacy"
        batch = batches.setdefault(
            batch_id,
            {
                "batchId": batch_id,
                "batchName": card.get("batchName") or ("历史卡密" if batch_id == "legacy" else "未命名批次"),
                "cardType": card.get("cardType", "slot"),
                "computeHours": float(card.get("computeHours") or 0),
                "slotDays": int(card.get("slotDays") or card.get("validDays") or 0),
                "count": 0,
                "unused": 0,
                "used": 0,
                "disabled": 0,
                "createdAt": card.get("createdAt", ""),
                "createdBy": card.get("createdBy", ""),
                "remark": card.get("remark", ""),
            },
        )
        batch["count"] += 1
        status = card_status(card)
        batch[status] = batch.get(status, 0) + 1
        if card.get("createdAt", "") > batch.get("createdAt", ""):
            batch["createdAt"] = card.get("createdAt", "")
    return sorted(batches.values(), key=lambda item: item.get("createdAt") or "", reverse=True)


def generate_card_code() -> str:
    return "KS-" + "-".join(secrets.token_hex(2).upper() for _ in range(4))


def apply_card_to_profile(profile: dict, card: dict, slot_id: str | None) -> tuple[dict, str]:
    card_type = card.get("cardType", "slot")
    compute_hours = float(card.get("computeHours") or 0)
    slot_days = int(card.get("slotDays") or card.get("validDays") or 0)
    messages = []
    if card_type in {"normal", "compute", "package"} and compute_hours > 0:
        profile["computeHours"] = float(profile.get("computeHours") or 0) + compute_hours
        profile["computeCards"] = [card["key"], *(profile.get("computeCards") or [])][:50]
        messages.append(f"算力 +{compute_hours:g}")
    if card_type in {"normal", "slot", "package"} and slot_days > 0:
        slots = profile.get("liveSlots") or []
        target = next((slot for slot in slots if slot.get("id") == slot_id), None) if slot_id else None
        target = target or (slots[0] if slots else None)
        if not target:
            target = default_live_slot(1)
            slots.append(target)
            profile["liveSlots"] = slots
        base = max(int(time.time() * 1000), int(float(target.get("expiresAt") or 0)))
        target["expiresAt"] = base + slot_days * 24 * 3600 * 1000
        target["redeemedCards"] = [card["key"], *(target.get("redeemedCards") or [])][:50]
        target["savedAt"] = now_iso()
        profile["activeLiveSlotId"] = target["id"]
        messages.append(f"{target.get('name', '直播位')} +{slot_days} 天")
    profile["savedAt"] = now_iso()
    return profile, "，".join(messages) or "卡密已兑换"


def normalize_text(text: str) -> str:
    return re.sub(r"\s+", " ", text.strip())


def is_system_comment_text(text: str) -> bool:
    value = normalize_text(str(text or ""))
    if not value:
        return True
    compact = re.sub(r"\s+", "", value)
    if re.fullmatch(r"\d+(?:\.\d+)?[wW万千kK]?(?:人)?(?:观看|在看|在线|观众|人气|热度)", compact):
        return True
    if re.fullmatch(r"(?:观看|在看|在线|观众|人气|热度|直播间观看人数)\d+(?:\.\d+)?[wW万千kK]?(?:人)?", compact):
        return True
    if re.search(r"\d+(?:\.\d+)?[wW万千kK]?(?:人)?(?:正在)?观看", compact):
        return True
    if re.search(r"(?:送出|赠送|收到|送了|进入直播间|加入直播间|关注了|点赞了|分享了|购买了|拍下|下单|加购|加入购物车)", compact):
        return True
    if re.search(r"(?:礼物|小心心|玫瑰|人气票|粉丝团|灯牌|红包|福袋|优惠券).*(?:x|X|×|\*)?\d+", compact):
        return True
    if re.fullmatch(r"(?:x|X|×|\*)?\d+", compact):
        return True
    return False


def is_system_comment_text(text: str) -> bool:
    value = normalize_text(str(text or ""))
    if not value:
        return True
    compact = re.sub(r"\s+", "", value)
    number_unit = r"(?:\d+(?:\.\d+)?(?:[wWkK]|\u4e07|\u5343)?(?:\u4eba)?)"
    view_prefix = r"(?:\u89c2\u770b|\u5728\u770b|\u5728\u7ebf|\u89c2\u4f17|\u4eba\u6c14|\u70ed\u5ea6|\u76f4\u64ad\u95f4\u89c2\u770b\u4eba\u6570)"
    view_suffix = r"(?:\u89c2\u770b|\u5728\u770b|\u5728\u7ebf|\u89c2\u4f17|\u4eba\u6c14|\u70ed\u5ea6)"
    event_words = (
        r"(?:\u9001\u51fa|\u8d60\u9001|\u6536\u5230|\u9001\u4e86|"
        r"\u8fdb\u5165\u76f4\u64ad\u95f4|\u52a0\u5165\u76f4\u64ad\u95f4|"
        r"\u5173\u6ce8\u4e86|\u70b9\u8d5e\u4e86|\u5206\u4eab\u4e86|"
        r"\u8d2d\u4e70\u4e86|\u62cd\u4e0b|\u4e0b\u5355|\u52a0\u8d2d|\u52a0\u5165\u8d2d\u7269\u8f66)"
    )
    gift_words = r"(?:\u793c\u7269|\u5c0f\u5fc3\u5fc3|\u73ab\u7470|\u4eba\u6c14\u7968|\u7c89\u4e1d\u56e2|\u706f\u724c|\u7ea2\u5305|\u798f\u888b|\u4f18\u60e0\u5238)"
    if re.fullmatch(number_unit + view_suffix, compact):
        return True
    if re.fullmatch(view_prefix + number_unit, compact):
        return True
    if re.search(number_unit + r"(?:\u6b63\u5728)?\u89c2\u770b", compact):
        return True
    if re.search(event_words, compact):
        return True
    if re.search(gift_words + r".*(?:x|X|\u00d7|\*)?\d+", compact):
        return True
    if re.fullmatch(r"(?:x|X|\u00d7|\*)?\d+", compact):
        return True
    return False


def parse_cloned_voice_items() -> list[dict]:
    items: list[dict] = []
    if not ALIYUN_CLONED_VOICES:
        return items
    try:
        data = json.loads(ALIYUN_CLONED_VOICES)
        if isinstance(data, list):
            source_items = data
        elif isinstance(data, dict):
            source_items = [data]
        else:
            source_items = []
        for index, item in enumerate(source_items, 1):
            if not isinstance(item, dict):
                continue
            voice_type = str(item.get("voice") or item.get("voiceType") or item.get("id") or "").strip()
            if not voice_type:
                continue
            name = str(item.get("name") or f"克隆音色 {index}").strip()
            gender = str(item.get("gender") or "自定义").strip()
            items.append(
                {
                    "name": name,
                    "voice": f"aliyun:{voice_type}",
                    "gender": gender,
                    "language": "中文",
                    "languageCode": "zh",
                    "locale": "zh-CN",
                    "scene": str(item.get("scene") or "克隆音色，适合中文直播口播").strip(),
                    "provider": "aliyun",
                    "voiceType": voice_type,
                    "clone": True,
                    "sourceCategory": "kesheng",
                }
            )
    except Exception:
        for index, raw in enumerate([part.strip() for part in ALIYUN_CLONED_VOICES.split(",") if part.strip()], 1):
            if ":" in raw:
                name, voice_type = [part.strip() for part in raw.split(":", 1)]
            else:
                name, voice_type = f"克隆音色 {index}", raw
            items.append(
                {
                    "name": name,
                    "voice": f"aliyun:{voice_type}",
                    "gender": "自定义",
                    "language": "中文",
                    "languageCode": "zh",
                    "locale": "zh-CN",
                    "scene": "克隆音色，适合中文直播口播",
                    "provider": "aliyun",
                    "voiceType": voice_type,
                    "clone": True,
                    "sourceCategory": "kesheng",
                }
            )
    return items


def aliyun_builtin_voices() -> list[dict]:
    return []


def load_voice_clone_jobs() -> list[dict]:
    data = read_json_file(VOICE_CLONE_JOBS_FILE, [])
    if not isinstance(data, list):
        return []
    normalized, changed = normalize_kesheng_shared_jobs(data)
    if changed:
        save_voice_clone_jobs(normalized)
    return normalized


def save_voice_clone_jobs(items: list[dict]):
    write_json_file(VOICE_CLONE_JOBS_FILE, items)


def voice_clone_sample_url(item: dict) -> str:
    sample_id = str(item.get("id") or "").strip()
    if not re.fullmatch(r"[a-f0-9]{32}", sample_id):
        return ""

    explicit = str(item.get("sampleAudioUrl") or item.get("sourceAudioUrl") or "").strip()
    if explicit:
        return explicit

    original_name = str(item.get("fileName") or "").strip()
    extension = Path(original_name).suffix.lower().lstrip(".")
    if extension not in {"wav", "mp3", "m4a", "ogg", "aac"}:
        return ""

    audio_path = AUDIO_DIR / f"{sample_id}.{extension}"
    return f"/audio/{audio_path.name}" if audio_path.exists() else ""


def delete_voice_clone_sample_file(item: dict) -> bool:
    sample_id = str(item.get("id") or "").strip()
    if not re.fullmatch(r"[a-f0-9]{32}", sample_id):
        return False
    extension = Path(str(item.get("fileName") or "")).suffix.lower().lstrip(".")
    if extension not in {"wav", "mp3", "m4a", "ogg", "aac"}:
        return False
    audio_path = AUDIO_DIR / f"{sample_id}.{extension}"
    if not audio_path.exists():
        return False
    audio_path.unlink()
    return True


def username_from_token(token: str | None) -> str:
    token = (token or "").strip()
    if not token:
        return ""
    session = load_sessions().get(token)
    username = str((session or {}).get("username") or "").strip()
    if is_super_admin_user(username):
        users = load_users()
        ensure_super_admin_user(users)
        save_users(users)
        return SUPER_ADMIN_USERNAME
    return username if username in load_users() else ""


def require_username_from_token(token: str | None) -> str:
    username = username_from_token(token)
    if not username:
        raise HTTPException(status_code=401, detail="请先登录")
    return username


def voice_clone_owner(item: dict) -> str:
    return str(item.get("owner") or "").strip().lower()


def is_shared_voice_clone_job(item: dict) -> bool:
    return is_super_admin_user(voice_clone_owner(item)) or str(item.get("sourceCategory") or "").strip().lower() == "kesheng"


def voice_clone_jobs_for_owner(owner: str) -> list[dict]:
    normalized_owner = (owner or "").strip().lower()
    if is_super_admin_user(normalized_owner):
        return shared_voice_clone_jobs()
    shared_ids = shared_voice_clone_ids() if not is_super_admin_user(normalized_owner) else set()
    return [
        item
        for item in load_voice_clone_jobs()
        if voice_clone_owner(item) == normalized_owner
        and (is_super_admin_user(normalized_owner) or str(item.get("voiceId") or "").strip() not in shared_ids)
        and not is_shared_voice_clone_job(item)
        and not is_removed_clone_voice(item)
    ]


def shared_voice_clone_jobs() -> list[dict]:
    return [
        item
        for item in load_voice_clone_jobs()
        if is_shared_voice_clone_job(item) and not is_removed_clone_voice(item)
    ]


def shared_voice_clone_ids() -> set[str]:
    return {
        str(item.get("voiceId") or "").strip()
        for item in shared_voice_clone_jobs()
        if str(item.get("voiceId") or "").strip()
    }


def normalize_kesheng_shared_jobs(items: list[dict]) -> tuple[list[dict], bool]:
    shared_ids = {
        str(item.get("voiceId") or "").strip()
        for item in items
        if is_shared_voice_clone_job(item) and str(item.get("voiceId") or "").strip()
    }
    changed = False
    normalized = []
    for item in items:
        voice_id = str(item.get("voiceId") or "").strip()
        should_share = is_shared_voice_clone_job(item) or (voice_id and voice_id in shared_ids)
        if should_share:
            if item.get("owner") != SUPER_ADMIN_USERNAME:
                item["owner"] = SUPER_ADMIN_USERNAME
                changed = True
            if item.get("sourceCategory") != "kesheng":
                item["sourceCategory"] = "kesheng"
                changed = True
        normalized.append(item)
    return normalized, changed


def is_removed_clone_voice(item: dict) -> bool:
    name = str(item.get("name") or "").lower()
    voice = str(item.get("voice") or item.get("voiceId") or item.get("voiceType") or "").lower()
    return "cherry" in name or "cherry" in voice or "阿里 qwen" in name


def voice_clone_jobs_as_voices(owner: str = "") -> list[dict]:
    voices = []
    source_items = []
    shared_items = shared_voice_clone_jobs()
    shared_ids = {
        str(item.get("voiceId") or "").strip()
        for item in shared_items
        if str(item.get("voiceId") or "").strip()
    }
    for item in shared_items:
        source_items.append({**item, "sourceCategory": "kesheng", "resolvedOwner": SUPER_ADMIN_USERNAME})
    if owner and not is_super_admin_user(owner):
        for item in voice_clone_jobs_for_owner(owner):
            if str(item.get("voiceId") or "").strip() in shared_ids:
                continue
            source_items.append({**item, "sourceCategory": "mine", "resolvedOwner": (owner or "").strip().lower()})
    for item in source_items:
        voice_id = str(item.get("voiceId") or "").strip()
        if not voice_id:
            continue
        raw_status = item.get("status")
        raw_status_text = str(raw_status or "").strip().lower()
        raw_status_code = item.get("rawStatus")
        raw_status_code_text = str(raw_status_code or "").strip().lower()
        is_shared = str(item.get("sourceCategory") or "").strip().lower() == "kesheng"
        is_ready = (
            is_shared
            or raw_status_text in {"ready", "success", "active", "completed", "complete", "ok", "可使用", "已完成"}
            or raw_status in {2, 4}
            or raw_status_code_text in {"ok", "ready", "success", "active", "completed", "complete"}
        )
        if not is_ready:
            continue
        voices.append(
            {
                "name": str(item.get("name") or "克隆音色")[:40],
                "voice": f"aliyun:{voice_id}",
                "gender": str(item.get("gender") or "自定义"),
                "language": "中文",
                "languageCode": "zh",
                "locale": "zh-CN",
                "scene": "克隆音色，适合中文直播口播",
                "provider": "aliyun",
                "voiceType": voice_id,
                "clone": True,
                "owner": str(item.get("resolvedOwner") or voice_clone_owner(item)).strip().lower(),
                "sourceCategory": str(item.get("sourceCategory") or "mine").strip().lower(),
            }
        )
    return voices


def available_voices(owner: str = "") -> list[dict]:
    voices = [dict(item, provider=item.get("provider", "edge")) for item in VOICES]
    voices.extend(parse_cloned_voice_items())
    voices.extend(voice_clone_jobs_as_voices(owner))
    deduped: dict[str, dict] = {}
    for item in voices:
        if is_removed_clone_voice(item):
            continue
        existing = deduped.get(item["voice"])
        if existing and existing.get("sourceCategory") == "kesheng" and item.get("sourceCategory") != "kesheng":
            continue
        deduped[item["voice"]] = item
    return list(deduped.values())


def voice_meta(voice: str, owner: str = "") -> dict | None:
    return next((item for item in available_voices(owner) if item["voice"] == voice), None)


def assert_voice_exists(voice: str, owner: str = ""):
    if not voice_meta(voice, owner):
        raise HTTPException(status_code=400, detail="音色不存在")


def load_compute_recharge_orders() -> dict[str, dict]:
    return read_json_file(COMPUTE_RECHARGE_ORDER_FILE, {})


def save_compute_recharge_orders():
    write_json_file(COMPUTE_RECHARGE_ORDER_FILE, COMPUTE_RECHARGE_ORDERS)


def compute_recharge_amount(hours: float) -> float:
    raw_hours = float(hours)
    if not raw_hours.is_integer():
        raise HTTPException(status_code=400, detail="充值算力只能是 50 的倍数")
    normalized_hours = int(raw_hours)
    if normalized_hours <= 0 or normalized_hours % COMPUTE_RECHARGE_UNIT_HOURS != 0:
        raise HTTPException(status_code=400, detail="充值算力只能是 50 的倍数")
    units = normalized_hours // COMPUTE_RECHARGE_UNIT_HOURS
    return float(units * COMPUTE_RECHARGE_UNIT_AMOUNT)


def compute_recharge_qr_data_url(code_url: str) -> str:
    try:
        import qrcode
    except ImportError as exc:
        raise HTTPException(status_code=500, detail="当前 Python 环境缺少 qrcode，无法生成支付二维码") from exc

    image = qrcode.make(code_url)
    buffer = io.BytesIO()
    image.save(buffer, format="PNG")
    return "data:image/png;base64," + base64.b64encode(buffer.getvalue()).decode("ascii")


def payment_attach(result: dict | None) -> dict:
    if not isinstance(result, dict):
        return {}
    raw_attach = result.get("attach")
    try:
        parsed = raw_attach if isinstance(raw_attach, dict) else json.loads(raw_attach)
        if not isinstance(parsed, dict):
            return {}
        return {
            **parsed,
            "type": parsed.get("type") or {"l": "live_slot_renewal", "c": "compute_recharge"}.get(parsed.get("t"), ""),
            "userId": parsed.get("userId") or parsed.get("u") or "",
            "slotId": parsed.get("slotId") or parsed.get("s") or "",
            "days": parsed.get("days") or parsed.get("d") or 0,
            "hours": parsed.get("hours") or parsed.get("h") or 0,
        }
    except (TypeError, ValueError, json.JSONDecodeError):
        return {}


def compact_payment_attach(order_type: str, *, user_id: str, slot_id: str = "", value: int | float = 0) -> str:
    payload = {"t": "l" if order_type == "live_slot_renewal" else "c", "u": str(user_id or "")}
    if order_type == "live_slot_renewal":
        payload.update({"s": str(slot_id or ""), "d": int(value)})
    else:
        payload["h"] = int(value) if float(value).is_integer() else float(value)
    encoded = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    if len(encoded.encode("utf-8")) > 128:
        raise HTTPException(status_code=400, detail="支付订单关联信息过长，请联系管理员检查用户或直播位ID")
    return encoded


def live_slot_renewal_plan(plan: str) -> dict:
    return LIVE_SLOT_RENEWAL_PLANS.get(plan) or LIVE_SLOT_RENEWAL_PLANS["monthly"]


def hydrate_payment_order(result: dict | None, order: dict | None = None) -> dict | None:
    if not isinstance(result, dict):
        return order
    order_id = str(result.get("out_trade_no") or (order or {}).get("orderId") or "").strip()
    if not order_id:
        return order
    target = order or COMPUTE_RECHARGE_ORDERS.get(order_id) or {"orderId": order_id}
    attach = payment_attach(result)
    order_type = str(attach.get("type") or target.get("type") or "compute_recharge").strip()
    username = safe_normalize_username(str(attach.get("username") or target.get("username") or ""))
    user_id = str(attach.get("userId") or target.get("userId") or "").strip()
    if order_type == "live_slot_renewal":
        target["type"] = "live_slot_renewal"
        target["slotId"] = str(attach.get("slotId") or target.get("slotId") or "").strip()
        target["days"] = int(attach.get("days") or target.get("days") or LIVE_SLOT_RENEWAL_DAYS)
        recovered_plan = "yearly" if int(target["days"]) >= 365 else "monthly"
        plan_meta = live_slot_renewal_plan(str(target.get("plan") or recovered_plan))
        target.setdefault("plan", recovered_plan)
        target.setdefault("planName", str(plan_meta["name"]))
        target.setdefault("amount", float(plan_meta["amount"]))
    else:
        target["type"] = "compute_recharge"
        target["hours"] = float(attach.get("hours") or target.get("hours") or 0)
    if username:
        target["username"] = username
    if user_id:
        target["userId"] = user_id
    if result.get("trade_state"):
        target["wechatTradeState"] = result.get("trade_state")
    target.setdefault("status", "pending")
    target.setdefault("createdAt", datetime.now(BEIJING_TZ).isoformat())
    COMPUTE_RECHARGE_ORDERS[order_id] = target
    save_compute_recharge_orders()
    return target


def resolve_payment_config_path() -> Path:
    candidates = [Path("/opt/backend/payment_config.json"), PAYMENT_CONFIG_PATH]
    for path in candidates:
        if path.exists():
            return path
    raise HTTPException(status_code=500, detail="未找到微信支付商户配置文件")


def get_wechatpay_client():
    global WECHATPAY_CLIENT
    if WECHATPAY_CLIENT is not None:
        return WECHATPAY_CLIENT

    try:
        from wechatpayv3 import WeChatPay, WeChatPayType
    except ImportError as exc:
        raise HTTPException(status_code=500, detail="当前 Python 环境缺少 wechatpayv3，无法创建支付订单") from exc

    config_path = resolve_payment_config_path()
    with open(config_path, "r", encoding="utf-8") as file:
        config = json.load(file)["wechat"]

    with open(config["key_path"], "r", encoding="utf-8") as file:
        private_key_content = file.read()
    with open(config["public_key_path"], "r", encoding="utf-8") as file:
        public_key_content = file.read()

    cert_dir = Path("/opt/backend/certs")
    if not cert_dir.exists():
        cert_dir = PAYMENT_CERT_DIR
    cert_dir.mkdir(parents=True, exist_ok=True)

    WECHATPAY_CLIENT = WeChatPay(
        wechatpay_type=WeChatPayType.NATIVE,
        mchid=config["mch_id"],
        appid=config["app_id"],
        private_key=private_key_content,
        cert_serial_no=config["cert_serial_no"],
        apiv3_key=config["api_v3_key"],
        cert_dir=str(cert_dir),
        public_key_id=config["public_key_id"],
        public_key=public_key_content,
    )
    return WECHATPAY_CLIENT


def get_wechat_notify_url() -> str:
    env_notify_url = os.getenv("WECHAT_NOTIFY_URL", "").strip()
    if env_notify_url:
        return env_notify_url

    with open(resolve_payment_config_path(), "r", encoding="utf-8") as file:
        config_notify_url = json.load(file)["wechat"].get("notify_url", "").strip()
    if config_notify_url:
        return config_notify_url

    if PUBLIC_BASE_URL:
        return f"{PUBLIC_BASE_URL}/api/compute-recharge/notify"
    return ""


def mark_compute_recharge_paid(order_id: str) -> dict | None:
    order = COMPUTE_RECHARGE_ORDERS.get(order_id)
    if not order:
        return None
    order["status"] = "success"
    order["paidAt"] = datetime.now(BEIJING_TZ).isoformat()
    if not order.get("appliedAt"):
        applied = apply_compute_recharge_order(order)
        if applied:
            order["appliedAt"] = datetime.now(BEIJING_TZ).isoformat()
    save_compute_recharge_orders()
    return order


def apply_compute_recharge_order(order: dict) -> dict | None:
    username = safe_normalize_username(str(order.get("username") or ""))
    user_id = str(order.get("userId") or "").strip()
    hours = float(order.get("hours") or 0)
    if not (user_id or username) or hours <= 0:
        return None
    users = load_users()
    user = next((item for item in users.values() if str(item.get("id") or "") == user_id), None) if user_id else None
    user = user or (ensure_super_admin_user(users) if is_super_admin_user(username) else users.get(username))
    if not user:
        return None
    username = user["username"]
    profile = normalize_user_profile(user.get("profile"), username)
    record_key = f"pay:{order.get('orderId', '')}"
    compute_cards = profile.get("computeCards") if isinstance(profile.get("computeCards"), list) else []
    if record_key not in compute_cards:
        profile["computeHours"] = float(profile.get("computeHours") or 0) + hours
        profile["computeCards"] = [record_key, *compute_cards][:100]
        profile["savedAt"] = now_iso()
        user["profile"] = normalize_user_profile(profile, username)
        user["updatedAt"] = now_iso()
        save_users(users)
    order["user"] = public_user(user)
    return order


def apply_live_slot_renewal_order(order: dict) -> dict | None:
    username = safe_normalize_username(str(order.get("username") or ""))
    user_id = str(order.get("userId") or "").strip()
    slot_id = str(order.get("slotId") or "").strip()
    days = int(order.get("days") or LIVE_SLOT_RENEWAL_DAYS)
    if not (user_id or username) or not slot_id or days <= 0:
        logger.error(
            "live renewal missing binding order=%s userId=%s username=%s slotId=%s days=%s",
            order.get("orderId"), user_id, username, slot_id, days,
        )
        return None
    users = load_users()
    user = next((item for item in users.values() if str(item.get("id") or "") == user_id), None) if user_id else None
    user = user or (ensure_super_admin_user(users) if is_super_admin_user(username) else users.get(username))
    if not user:
        logger.error("live renewal user not found order=%s userId=%s username=%s", order.get("orderId"), user_id, username)
        return None
    username = user["username"]
    profile = normalize_user_profile(user.get("profile"), username)
    slots = profile.get("liveSlots") or []
    target = next((slot for slot in slots if slot.get("id") == slot_id), None)
    if not target:
        logger.error("live renewal slot not found order=%s userId=%s slotId=%s", order.get("orderId"), user.get("id"), slot_id)
        return None
    record_key = f"pay:{order.get('orderId', '')}"
    redeemed_cards = target.get("redeemedCards") if isinstance(target.get("redeemedCards"), list) else []
    if record_key not in redeemed_cards:
        base = max(int(time.time() * 1000), int(float(target.get("expiresAt") or 0)))
        target["expiresAt"] = base + days * 24 * 3600 * 1000
        target["redeemedCards"] = [record_key, *redeemed_cards][:50]
        target["savedAt"] = now_iso()
        profile["savedAt"] = now_iso()
        user["profile"] = normalize_user_profile(profile, username)
        user["updatedAt"] = now_iso()
        save_users(users)
    order["user"] = public_user(user)
    order["userId"] = str(user.get("id") or "")
    order["username"] = username
    order["slotName"] = target.get("name", order.get("slotName", "直播位"))
    order["expiresAt"] = int(float(target.get("expiresAt") or 0))
    logger.info(
        "live renewal applied order=%s userId=%s username=%s slotId=%s expiresAt=%s",
        order.get("orderId"), user.get("id"), username, slot_id, order["expiresAt"],
    )
    return order


def mark_live_slot_renewal_paid(order_id: str) -> dict | None:
    order = COMPUTE_RECHARGE_ORDERS.get(order_id)
    if not order:
        return None
    order["paymentStatus"] = "success"
    order["paidAt"] = datetime.now(BEIJING_TZ).isoformat()
    if not order.get("appliedAt") or not int(float(order.get("expiresAt") or 0)):
        applied = apply_live_slot_renewal_order(order)
        if applied:
            order.setdefault("appliedAt", datetime.now(BEIJING_TZ).isoformat())
    if order.get("appliedAt") and int(float(order.get("expiresAt") or 0)) > 0:
        order["status"] = "success"
        order.pop("reason", None)
    else:
        order["status"] = "paid_unapplied"
        order["reason"] = "微信已确认付款，但尚未定位到对应用户直播位，系统将继续补发"
    save_compute_recharge_orders()
    return order


def mark_payment_order_paid(order_id: str) -> dict | None:
    order = COMPUTE_RECHARGE_ORDERS.get(order_id)
    if not order:
        return None
    if order.get("type") == "live_slot_renewal":
        return mark_live_slot_renewal_paid(order_id)
    return mark_compute_recharge_paid(order_id)


COMPUTE_RECHARGE_ORDERS.update(load_compute_recharge_orders())


def reconcile_paid_orders():
    changed = False
    for order_id, order in list(COMPUTE_RECHARGE_ORDERS.items()):
        paid = order.get("status") in {"success", "paid_unapplied"} or order.get("paymentStatus") == "success"
        if not paid or order.get("appliedAt"):
            continue
        try:
            applied = mark_payment_order_paid(order_id)
            changed = bool(applied and applied.get("appliedAt")) or changed
        except Exception:
            continue
    if changed:
        save_compute_recharge_orders()


reconcile_paid_orders()


RISKY_REPLACEMENTS = {
    "绝对": "比较",
    "第一": "靠前",
    "唯一": "比较特别",
    "永久": "较长时间",
    "100%": "尽量",
    "稳赚": "更稳妥",
    "包治": "帮助改善",
    "根治": "改善",
    "特效": "有针对性",
    "国家级": "有品质感",
}


def soften_risky_terms(text: str) -> str:
    for source, target in RISKY_REPLACEMENTS.items():
        text = text.replace(source, target)
    return text


def normalize_forbidden_words(words: list[str] | None) -> list[str]:
    normalized: list[str] = []
    seen: set[str] = set()
    for word in words or []:
        cleaned = normalize_text(str(word))[:40]
        key = cleaned.lower()
        if not cleaned or key in seen:
            continue
        seen.add(key)
        normalized.append(cleaned)
        if len(normalized) >= 100:
            break
    return normalized


def forbidden_words_prompt(words: list[str] | None) -> str:
    items = normalize_forbidden_words(words)
    if not items:
        return ""
    return "违禁词限制：最终输出严禁出现以下词语或近似原样表达，必须换成中性、合规、温和表述：" + "、".join(items) + "\n"


def apply_forbidden_words(text: str, words: list[str] | None) -> str:
    result = normalize_text(text)
    for word in normalize_forbidden_words(words):
        replacement = "相关表述"
        if re.search(r"[A-Za-z0-9]", word):
            result = re.sub(re.escape(word), replacement, result, flags=re.IGNORECASE)
        else:
            result = result.replace(word, replacement)
    return result


def local_script(text: str, style: str, mode: str) -> str:
    text = soften_risky_terms(normalize_text(text))
    openers = {
        "带货": "家人们，今天这段内容我给大家讲得更直接一点。",
        "知识": "接下来我们用更清楚的方式把重点讲明白。",
        "情感": "如果你正在听这段内容，可以先放轻松，我们慢慢说。",
        "客服": "您好，这里帮您把重点整理成更容易理解的说法。",
    }
    closers = {
        "带货": "如果你觉得合适，可以先关注重点信息，再根据自己的需要选择。",
        "知识": "这样理解起来会更连贯，也更适合持续直播讲解。",
        "情感": "希望这段表达听起来更自然，也更容易让人接受。",
        "客服": "如需进一步确认，可以继续补充问题，我会按步骤说明。",
    }
    if mode == "generate":
        return (
            f"{openers[style]}先和大家说一下今天的重点信息：{text}。"
            "如果你刚进直播间，可以先停留一会儿听我讲完，因为这段内容更适合我们边听边判断是不是适合自己。"
            "它的核心价值不是让大家冲动决定，而是把关键信息讲清楚，让你知道它适合什么场景、解决什么问题、使用时要注意什么。"
            "从直播间讲解的角度看，我们会把重点放在真实需求上：如果你正好有类似需要，可以重点关注它的使用体验、适用人群和后续安排；"
            "如果你还在对比，也可以先把这段介绍听完，再结合自己的预算、习惯和实际情况来判断。"
            "接下来可以从三个方向理解：一是看它是否匹配你的日常场景；二是看它能不能减少你的选择成本；三是看当前信息是否足够清楚。"
            "大家有问题也可以直接在评论区打出来，比如适不适合自己、怎么选择、需要注意哪些细节，我会按照问题逐条整理成更容易听懂的话术。"
            f"最后再提醒一下，所有选择都建议以自己的实际情况为准，不盲目跟风。{closers[style]}"
        )

    sentences = re.split(r"(?<=[。！？!?])", text)
    body = "".join(sentence.strip() for sentence in sentences if sentence.strip())
    return f"{openers[style]}{body}{closers[style]}"


def build_script_prompt(text: str, style: str, mode: str, forbidden_words: list[str] | None = None) -> str:
    return (
        "你是直播音频脚本文案助理，只输出最终中文直播口播文案，不要标题、解释、列表编号或修改说明。\n"
        f"目标风格：{STYLE_PROMPTS[style]}\n"
        f"任务要求：{SCRIPT_MODE_PROMPTS[mode]}\n"
        f"{forbidden_words_prompt(forbidden_words)}"
        f"用户信息或原文：{text}"
    )


def build_translation_prompt(text: str, style: str, target: str, forbidden_words: list[str] | None = None) -> str:
    target_meta = TRANSLATION_TARGETS[target]
    if target == "zh":
        task = "把原文优化成自然、流畅、适合直播间直接播报的中文，不改变核心意思和关键顺序。"
    else:
        task = f"把中文直播口播文案翻译成自然、地道、适合直播间直接播报的{target_meta['language']}。"
    return (
        "你是直播脚本多语种翻译助理，只输出最终文案，不要标题、解释、列表编号、引号或 Markdown。\n"
        f"目标任务：{task}\n"
        f"目标风格：{STYLE_PROMPTS[style]}\n"
        "要求：保留原文卖点、节奏和行动引导；不要新增原文没有的价格、功效、资质、库存、销量或承诺；"
        "主动弱化绝对化、医疗化、收益保证等高风险表达；输出内容要适合直接交给对应语种 TTS 播放。\n"
        f"{forbidden_words_prompt(forbidden_words)}"
        f"原文：{text}"
    )


def call_translate(text: str, style: str, target: str, forbidden_words: list[str] | None = None) -> tuple[str | None, str]:
    prompt = build_translation_prompt(text, style, target, forbidden_words)
    errors: list[str] = []

    if target != "zh":
        try:
            ark_translation = call_ark_translation(text, target, timeout=25) if len(text) <= 120 else None
            if ark_translation:
                validate_translated_text(ark_translation, target)
                return ark_translation, "ark-translation"
        except Exception as exc:
            errors.append(f"ark-translation: {exc}")

    try:
        ark_text = call_ark_prompt(prompt, timeout=45) if target == "zh" else call_ark_prompt_translation_chunked(text, style, target, forbidden_words, timeout=30)
        if ark_text:
            validate_translated_text(ark_text, target)
            return ark_text, "ark"
    except Exception as exc:
        errors.append(f"ark: {exc}")

    try:
        deepseek_text = call_deepseek_prompt(prompt, timeout=45)
        if deepseek_text:
            validate_translated_text(deepseek_text, target)
            return deepseek_text, "deepseek"
    except Exception as exc:
        errors.append(f"deepseek: {exc}")

    if errors:
        raise RuntimeError("；".join(errors))
    return None, current_model_provider()


def build_live_line_prompt(text: str, style: str, mode: str, round_index: int, forbidden_words: list[str] | None = None) -> str:
    mode_text = {
        "off": "保持原句，不做扩写，只做必要的风险词柔化。",
        "full-free": "在不改变核心意思的前提下重写这一句，表达要和上一次明显不同，但不要加入用户没有提供的硬信息。",
        "semi-free": "在不改变核心意思和语气的前提下轻微改写这一句，保留相似度，但避免每轮完全一样。",
        "ai-interrupt": "保留为 AI 插话播放入口，当前先按半自由方式轻微改写。",
    }[mode]
    return (
        "你是直播间逐句口播助理，只输出一句适合直接播报的中文文案，不要解释、标题或编号。\n"
        f"目标风格：{STYLE_PROMPTS[style]}\n"
        f"当前轮次：第 {round_index} 轮。\n"
        f"处理规则：{mode_text}\n"
        "要求：口语自然、适合直播间播放，主动规避绝对化、夸大承诺、医疗化、收益保证等风险表达。\n"
        f"{forbidden_words_prompt(forbidden_words)}"
        f"原句：{text}"
    )


def local_live_line(text: str, mode: str, round_index: int) -> str:
    text = soften_risky_terms(normalize_text(text))
    if mode == "off" or round_index <= 1:
        return text

    variants = [
        ("", "大家可以重点听一下。"),
        ("换个更自然的说法，", "可以结合自己的实际情况判断。"),
        ("简单来说，", "这点比较适合反复听一遍。"),
        ("再给大家补一句，", "有问题也可以继续在评论区问。"),
    ]
    prefix, suffix = variants[round_index % len(variants)]
    if mode == "semi-free":
        return f"{prefix}{text}"
    return f"{prefix}{text}{suffix}"


def new_douyin_capture_state(platform: str = "douyin") -> dict:
    return {
        "running": False,
        "platform": platform,
        "url": "",
        "status": "未连接",
        "error": "",
        "statusDetail": "",
        "lastEvent": "未连接",
        "lastEventAt": 0,
        "events": deque(maxlen=20),
        "comments": deque(maxlen=200),
        "lastCommentAt": 0,
        "lastComment": "",
        "messageCount": 0,
        "commentCount": 0,
        "seenCommentIds": deque(maxlen=500),
        "roomId": "",
        "startedAt": 0,
        "stoppedAt": 0,
        "fetcher": None,
        "thread": None,
    }


def douyin_capture_context(token: str, slot_id: str, *, create: bool = True, platform: str | None = None) -> tuple[str, dict]:
    _, user = get_user_by_token(token)
    profile = normalize_user_profile(user.get("profile"), user["username"])
    require_live_slot(profile, slot_id)
    key = f"{user.get('id') or user['username']}:{slot_id}"
    with DOUYIN_CAPTURES_LOCK:
        state = DOUYIN_CAPTURES.get(key)
        if state is None and create:
            state = new_douyin_capture_state(platform or "douyin")
            DOUYIN_CAPTURES[key] = state
        elif state is not None and platform is not None:
            state["platform"] = platform
    return key, state or new_douyin_capture_state()


def mark_douyin_event(state: dict, status: str, detail: str = "", *, is_error: bool = False):
    now = int(time.time())
    state["status"] = status
    state["statusDetail"] = detail
    state["lastEvent"] = status
    state["lastEventAt"] = now
    state["error"] = detail or status if is_error else ""
    events = state.get("events")
    if events is None:
        events = deque(maxlen=20)
        state["events"] = events
    events.append({
        "time": now,
        "status": status,
        "detail": detail,
        "level": "error" if is_error else "info",
    })


def enqueue_comment(state: dict, comment: dict):
    content = normalize_text(str(comment.get("content", "")))
    nickname = normalize_text(str(comment.get("nickname") or "瑙備紬"))[:40]
    if not content or is_system_comment_text(content) or is_system_comment_text(nickname):
        return
    comment_id = str(comment.get("comment_id") or comment.get("commentId") or "").strip()
    seen_ids = state.get("seenCommentIds")
    if seen_ids is None:
        seen_ids = deque(maxlen=500)
        state["seenCommentIds"] = seen_ids
    if comment_id and comment_id in seen_ids:
        return
    if comment_id:
        seen_ids.append(comment_id)
    item = {
        "id": uuid.uuid4().hex,
        "nickname": normalize_text(str(comment.get("nickname") or "观众"))[:40],
        "content": content[:300],
        "user_id": str(comment.get("user_id") or ""),
        "comment_id": comment_id,
        "platform": str(comment.get("platform") or state.get("platform") or "douyin"),
        "type": str(comment.get("type") or "chat"),
        "created_at": int(time.time()),
    }
    state["comments"].append(item)
    state["commentCount"] = int(state.get("commentCount") or 0) + 1
    state["messageCount"] = int(state.get("messageCount") or 0) + 1
    state["lastCommentAt"] = item["created_at"]
    state["lastComment"] = f"{item['nickname']}：{item['content']}"
    platform_name = PLATFORM_LABELS.get(state.get("platform", "douyin"), "评论")
    mark_douyin_event(state, "采集中", f"已收到{platform_name}评论")


def douyin_runtime_check() -> dict:
    now = int(time.time())
    cached = DOUYIN_RUNTIME_CACHE.get("data")
    if cached and now - int(DOUYIN_RUNTIME_CACHE.get("checkedAt") or 0) < 30:
        return cached
    files = {
        "projectDir": DOUYIN_PROJECT_DIR.exists(),
        "danmuFetcher": (DOUYIN_PROJECT_DIR / "core" / "danmu_fetcher.py").exists(),
        "signJs": (DOUYIN_PROJECT_DIR / "sign.js").exists(),
        "protobuf": (DOUYIN_PROJECT_DIR / "protobuf" / "douyin.py").exists(),
    }
    modules = {}
    for name, import_name in {
        "requests": "requests",
        "websocket-client": "websocket",
        "execjs": "execjs",
        "betterproto": "betterproto",
    }.items():
        try:
            __import__(import_name)
            modules[name] = True
        except Exception:
            modules[name] = False
    node_ok = False
    try:
        node_check = subprocess.run(["node", "-v"], capture_output=True, text=True, timeout=3)
        node_ok = node_check.returncode == 0
    except Exception:
        node_ok = False
    data = {"files": files, "modules": modules, "node": node_ok, "ok": all(files.values()) and all(modules.values()) and node_ok}
    DOUYIN_RUNTIME_CACHE.update({"checkedAt": now, "data": data})
    return data


def douyin_status(state: dict) -> dict:
    thread = state.get("thread")
    thread_alive = bool(thread and thread.is_alive())
    platform = state.get("platform", "douyin")
    active_statuses = {"连接中", "启动中", "正在解析直播间", "已解析直播间", "正在连接 WebSocket", "采集中", "收到消息"}
    external_platform = platform != "douyin"
    if state.get("running") and not thread_alive and not external_platform:
        state["running"] = False
        state["stoppedAt"] = int(time.time())
        if not state.get("error"):
            mark_douyin_event(state, "采集已断开", "采集线程未存活，未收到可用评论", is_error=True)
    if not state.get("running") and state.get("status") in active_statuses and not state.get("error") and not external_platform:
        mark_douyin_event(state, "采集未运行", "采集线程未存活，未收到可用评论", is_error=True)
    return {
        "running": bool(state["running"]),
        "threadAlive": thread_alive or external_platform,
        "platform": platform,
        "platformName": PLATFORM_LABELS.get(platform, "抖音"),
        "url": state["url"],
        "status": state["status"],
        "error": state["error"],
        "statusDetail": state.get("statusDetail", ""),
        "lastEvent": state.get("lastEvent", ""),
        "lastEventAt": state.get("lastEventAt", 0),
        "events": list(state.get("events") or [])[-20:],
        "lastCommentAt": state.get("lastCommentAt", 0),
        "lastComment": state.get("lastComment", ""),
        "messageCount": state.get("messageCount", 0),
        "commentCount": state.get("commentCount", 0),
        "roomId": state.get("roomId", ""),
        "startedAt": state.get("startedAt", 0),
        "stoppedAt": state.get("stoppedAt", 0),
        "queueSize": len(state.get("comments") or []),
        "projectDir": str(DOUYIN_PROJECT_DIR) if platform == "douyin" else "",
        "runtime": douyin_runtime_check() if platform == "douyin" else {"ok": True, "mode": "browser-extension"},
    }


def start_external_capture(state: dict, platform: str, url: str = "") -> dict:
    now = int(time.time())
    state.update({
        "running": True,
        "platform": platform,
        "url": url or state.get("url", ""),
        "error": "",
        "status": "等待插件连接",
        "statusDetail": "请在浏览器插件中绑定当前账号和直播位，并打开快手直播后台评论页。",
        "startedAt": now,
        "stoppedAt": 0,
        "fetcher": None,
        "thread": None,
    })
    mark_douyin_event(state, "等待插件连接", state["statusDetail"])
    return douyin_status(state)


def ingest_external_comment(payload: ExternalCommentIngestRequest) -> dict:
    _, state = douyin_capture_context(payload.token, payload.slotId, platform=payload.platform)
    state["running"] = True
    state["platform"] = payload.platform
    if payload.url:
        state["url"] = payload.url
    if payload.roomId:
        state["roomId"] = payload.roomId
    if not state.get("startedAt"):
        state["startedAt"] = int(time.time())
    enqueue_comment(state, {
        "nickname": payload.nickname,
        "content": payload.content,
        "comment_id": payload.commentId,
        "user_id": payload.userId,
        "platform": payload.platform,
    })
    return douyin_status(state)


def start_douyin_fetcher(state: dict, url: str) -> dict:
    stop_douyin_fetcher(state)
    started_at = int(time.time())
    state.update({
        "platform": "douyin",
        "url": url,
        "running": True,
        "error": "",
        "statusDetail": "",
        "lastEvent": "准备启动",
        "lastEventAt": started_at,
        "events": deque(maxlen=20),
        "lastCommentAt": 0,
        "lastComment": "",
        "messageCount": 0,
        "commentCount": 0,
        "roomId": "",
        "startedAt": started_at,
        "stoppedAt": 0,
        "fetcher": None,
        "thread": None,
    })

    if not DOUYIN_PROJECT_DIR.exists():
        state["running"] = False
        mark_douyin_event(state, "采集不可用", "未找到转播项目目录", is_error=True)
        return douyin_status(state)

    if str(DOUYIN_PROJECT_DIR) not in sys.path:
        sys.path.insert(0, str(DOUYIN_PROJECT_DIR))

    try:
        from core.danmu_fetcher import DouyinDanmuFetcher
    except Exception as exc:
        state["running"] = False
        mark_douyin_event(state, "采集不可用", f"采集依赖未就绪：{exc}", is_error=True)
        return douyin_status(state)

    def run_fetcher():
        fetcher = None

        def update_fetcher_status(status: str, detail: str = ""):
            current_fetcher = state.get("fetcher")
            if current_fetcher is not fetcher:
                return
            is_error = any(flag in status for flag in ("错误", "失败", "异常"))
            if detail.startswith("roomId="):
                state["roomId"] = detail.replace("roomId=", "", 1)
            if status == "收到消息" and detail:
                state["messageCount"] = int(state.get("messageCount") or 0) + 1
            mark_douyin_event(state, status, detail, is_error=is_error)

        try:
            def on_danmu(danmu: dict):
                if state.get("fetcher") is fetcher and state.get("running"):
                    enqueue_comment(state, danmu)

            try:
                fetcher = DouyinDanmuFetcher(on_danmu_callback=on_danmu, on_status_callback=update_fetcher_status)
            except TypeError:
                fetcher = DouyinDanmuFetcher(on_danmu_callback=on_danmu)
                mark_douyin_event(state, "兼容采集器", "当前采集器不支持状态回调，已使用转播项目兼容方式")

            state["fetcher"] = fetcher
            if not fetcher.set_room(url):
                state["running"] = False
                mark_douyin_event(state, "链接无效", "请输入 live.douyin.com 直播间链接", is_error=True)
                return

            mark_douyin_event(state, "正在解析直播间", "正在获取 roomId")
            try:
                room_id = fetcher.room_id
            except Exception as exc:
                room_id = ""
                mark_douyin_event(state, "房间解析失败", str(exc), is_error=True)
            if room_id:
                state["roomId"] = str(room_id)
                mark_douyin_event(state, "已解析直播间", f"roomId={room_id}")
            else:
                mark_douyin_event(state, "开始拉取弹幕", "未预先解析到 roomId，交给采集器继续尝试")

            fetcher.start()
        except Exception as exc:
            if state.get("fetcher") is fetcher:
                mark_douyin_event(state, "采集异常", str(exc), is_error=True)
        finally:
            if state.get("fetcher") is fetcher:
                state["running"] = False
                state["stoppedAt"] = int(time.time())
                if not state.get("error"):
                    mark_douyin_event(state, "采集已断开", state.get("statusDetail") or "采集线程已结束", is_error=True)

    thread = threading.Thread(target=run_fetcher, daemon=True)
    state.update({"thread": thread})
    mark_douyin_event(state, "采集中", "采集线程已启动，正在后台连接直播间")
    thread.start()
    return douyin_status(state)


def stop_douyin_fetcher(state: dict) -> dict:
    fetcher = state.get("fetcher")
    if fetcher:
        try:
            fetcher.stop()
        except Exception:
            pass
    state.update({"running": False, "stoppedAt": int(time.time()), "fetcher": None, "thread": None})
    mark_douyin_event(state, "已停止", "")
    return douyin_status(state)


def build_comment_reply_prompt(comment: str, nickname: str, script: str, style: str, forbidden_words: list[str] | None = None) -> str:
    return (
        "你是直播间 AI 主播评论回复助理，只输出一句适合直接播报的中文回复，不要解释、标题或编号。\n"
        f"目标风格：{STYLE_PROMPTS[style]}\n"
        "回复规则：先判断评论是否和直播话术内容、近义内容、产品信息、适用场景、优惠引导或常见疑问相关。"
        "如果相关，就结合话术内容自然回复；如果不相关，就用一句温和的话带回直播主题。"
        "不要在回复开头重复观众昵称，前端会统一加称呼。"
        "不要编造价格、资质、库存、销量、功效或承诺；主动规避绝对化、医疗化、收益保证等风险表达。\n"
        f"{forbidden_words_prompt(forbidden_words)}"
        f"观众昵称：{nickname}\n"
        f"观众评论：{comment}\n"
        f"当前直播话术：{script[:3000]}"
    )


def local_comment_reply(comment: str, nickname: str, script: str) -> str:
    comment = soften_risky_terms(normalize_text(comment))
    script = soften_risky_terms(normalize_text(script))
    lead = script[:80] if script else "当前直播间的重点内容"
    return f"你这个问题我看到了，简单说就是可以结合刚才讲到的重点来看：{lead}。如果你还有具体场景，也可以继续打在评论区。"


def beijing_time_text(prefix: str = "") -> str:
    now = datetime.now(BEIJING_TZ)
    clean_prefix = normalize_text(prefix)
    if clean_prefix and "北京时间" not in clean_prefix:
        return f"{clean_prefix}，现在是北京时间 {now.hour} 点 {now.minute:02d} 分了。"
    return f"现在是北京时间 {now.hour} 点 {now.minute:02d} 分了。"


def call_ark_prompt(prompt: str, timeout: int = 30) -> str | None:
    api_key = os.getenv("ARK_API_KEY", "").strip()
    model = os.getenv("ARK_MODEL", "").strip()
    if not api_key or not model:
        return None
    base_url = os.getenv("ARK_BASE_URL", "https://ark.cn-beijing.volces.com/api/v3").rstrip("/")
    payload = {
        "model": model,
        "input": [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}],
    }
    response = requests.post(
        f"{base_url}/responses",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=timeout,
    )
    response.raise_for_status()
    return extract_ark_response_text(response.json())


def call_ark_translation(text: str, target: str, timeout: int = 60) -> str | None:
    api_key = os.getenv("ARK_API_KEY", "").strip()
    if not api_key:
        return None
    model = os.getenv("ARK_TRANSLATION_MODEL", "doubao-seed-translation-250915").strip() or "doubao-seed-translation-250915"
    base_url = os.getenv("ARK_BASE_URL", "https://ark.cn-beijing.volces.com/api/v3").rstrip("/")
    payload = {
        "model": model,
        "input": [
            {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": text,
                        "translation_options": {
                            "source_language": "zh",
                            "target_language": target,
                        },
                    }
                ],
            }
        ],
    }
    response = requests.post(
        f"{base_url}/responses",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=timeout,
    )
    response.raise_for_status()
    translated = extract_ark_response_text(response.json()).strip()
    validate_translated_text(translated, target)
    return translated


def split_translation_text(text: str, max_chars: int = 140) -> list[str]:
    normalized = normalize_text(text)
    if len(normalized) <= max_chars:
        return [normalized] if normalized else []
    chunks: list[str] = []
    current = ""
    sentence_breaks = set("。！？!?；;\n")
    for char in normalized:
        current += char
        if char in sentence_breaks or len(current) >= max_chars:
            part = current.strip()
            if part:
                chunks.append(part)
            current = ""
    if current.strip():
        chunks.append(current.strip())
    balanced: list[str] = []
    for chunk in chunks:
        if len(chunk) <= max_chars:
            balanced.append(chunk)
            continue
        for index in range(0, len(chunk), max_chars):
            part = chunk[index:index + max_chars].strip()
            if part:
                balanced.append(part)
    return balanced


def call_ark_translation_chunked(text: str, target: str, timeout: int = 45) -> str | None:
    chunks = split_translation_text(text)
    if not chunks:
        return None
    translated_parts = []
    for chunk in chunks:
        translated_parts.append(call_ark_translation(chunk, target, timeout=timeout) or "")
    translated = "\n".join(part.strip() for part in translated_parts if part.strip()).strip()
    validate_translated_text(translated, target)
    return translated


def call_ark_prompt_translation_chunked(
    text: str,
    style: str,
    target: str,
    forbidden_words: list[str] | None = None,
    timeout: int = 30,
) -> str | None:
    chunks = split_translation_text(text)
    if not chunks:
        return None
    unique_chunks = list(dict.fromkeys(chunks))

    def translate_one(chunk: str) -> tuple[str, str]:
        try:
            translated = call_ark_translation(chunk, target, timeout=min(timeout, 25))
        except Exception:
            prompt = build_translation_prompt(chunk, style, target, forbidden_words)
            translated = call_ark_prompt(prompt, timeout=timeout)
            validate_translated_text(translated or "", target)
        return chunk, (translated or "").strip()

    translated_map: dict[str, str] = {}
    errors: list[str] = []
    with ThreadPoolExecutor(max_workers=min(4, len(unique_chunks))) as executor:
        futures = [executor.submit(translate_one, chunk) for chunk in unique_chunks]
        for future in as_completed(futures):
            try:
                chunk, translated = future.result()
                translated_map[chunk] = translated
            except Exception as exc:
                errors.append(str(exc))
    if errors:
        raise RuntimeError("；".join(errors[:3]))
    translated_text = "\n".join(translated_map.get(chunk, "") for chunk in chunks if translated_map.get(chunk, "")).strip()
    validate_translated_text(translated_text, target)
    return translated_text


def call_deepseek_prompt(prompt: str, timeout: int = 30) -> str | None:
    api_key = os.getenv("DEEPSEEK_API_KEY", "").strip()
    if not api_key:
        return None
    payload = {
        "model": os.getenv("DEEPSEEK_MODEL", "deepseek-chat"),
            "messages": [
            {"role": "system", "content": "你是直播间 AI 主播助理，只输出可直接播报的内容。"},
            {"role": "user", "content": prompt},
            ],
            "temperature": 0.7,
        "stream": False,
    }
    response = requests.post(
        "https://api.deepseek.com/chat/completions",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=timeout,
    )
    response.raise_for_status()
    return response.json()["choices"][0]["message"]["content"].strip()


def extract_ark_response_text(data: dict) -> str:
    if isinstance(data.get("output_text"), str) and data["output_text"].strip():
        return data["output_text"].strip()

    for output in data.get("output", []):
        for content in output.get("content", []):
            text = content.get("text")
            if isinstance(text, str) and text.strip():
                return text.strip()

    choices = data.get("choices", [])
    if choices:
        message = choices[0].get("message", {})
        content = message.get("content")
        if isinstance(content, str) and content.strip():
            return content.strip()

    raise ValueError("火山模型返回为空")


def validate_translated_text(text: str, target: str):
    clean = (text or "").strip()
    if not clean:
        raise ValueError("翻译结果为空")
    compact = clean.replace("\n", "").strip()
    if compact and set(compact) == {"?"}:
        raise ValueError("翻译结果异常，返回了问号内容")
    if target == "zh":
        return
    script_checks = {
        "ja": r"[\u3040-\u30ff]",
        "ko": r"[\uac00-\ud7af]",
        "ru": r"[\u0400-\u04ff]",
    }
    pattern = script_checks.get(target)
    if pattern and not re.search(pattern, clean):
        raise ValueError(f"翻译结果不像目标语种：{target}")
    if target != "ja":
        chinese_chars = len(re.findall(r"[\u4e00-\u9fff]", clean))
        if chinese_chars >= max(6, len(clean) * 0.2):
            raise ValueError("翻译结果仍包含大量中文")


def call_ark(text: str, style: str, mode: str, forbidden_words: list[str] | None = None) -> str | None:
    api_key = os.getenv("ARK_API_KEY", "").strip()
    model = os.getenv("ARK_MODEL", "").strip()
    if not api_key or not model:
        return None

    base_url = os.getenv("ARK_BASE_URL", "https://ark.cn-beijing.volces.com/api/v3").rstrip("/")
    prompt = build_script_prompt(text, style, mode, forbidden_words)
    payload = {
        "model": model,
        "input": [
            {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": prompt,
                    }
                ],
            }
        ],
    }
    response = requests.post(
        f"{base_url}/responses",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=45,
    )
    response.raise_for_status()
    return extract_ark_response_text(response.json())


def call_deepseek(text: str, style: str, mode: str, forbidden_words: list[str] | None = None) -> str | None:
    api_key = os.getenv("DEEPSEEK_API_KEY", "").strip()
    if not api_key:
        return None

    payload = {
        "model": os.getenv("DEEPSEEK_MODEL", "deepseek-chat"),
        "messages": [
            {
                "role": "system",
                "content": "你是直播音频脚本文案助理，只输出最终中文直播口播文案，不要解释。",
            },
            {
                "role": "user",
                "content": build_script_prompt(text, style, mode, forbidden_words),
            },
        ],
        "temperature": 0.7,
        "stream": False,
    }
    response = requests.post(
        "https://api.deepseek.com/chat/completions",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=45,
    )
    response.raise_for_status()
    data = response.json()
    return data["choices"][0]["message"]["content"].strip()


def call_ark_live_line(text: str, style: str, mode: str, round_index: int, forbidden_words: list[str] | None = None) -> str | None:
    api_key = os.getenv("ARK_API_KEY", "").strip()
    model = os.getenv("ARK_MODEL", "").strip()
    if not api_key or not model or mode == "off":
        return None

    base_url = os.getenv("ARK_BASE_URL", "https://ark.cn-beijing.volces.com/api/v3").rstrip("/")
    payload = {
        "model": model,
        "input": [
            {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": build_live_line_prompt(text, style, mode, round_index, forbidden_words),
                    }
                ],
            }
        ],
    }
    response = requests.post(
        f"{base_url}/responses",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=30,
    )
    response.raise_for_status()
    return extract_ark_response_text(response.json())


def call_deepseek_live_line(text: str, style: str, mode: str, round_index: int, forbidden_words: list[str] | None = None) -> str | None:
    api_key = os.getenv("DEEPSEEK_API_KEY", "").strip()
    if not api_key or mode == "off":
        return None

    payload = {
        "model": os.getenv("DEEPSEEK_MODEL", "deepseek-chat"),
        "messages": [
            {
                "role": "system",
                "content": "你是直播间逐句口播助理，只输出一句适合直接播放的中文文案。",
            },
            {
                "role": "user",
                "content": build_live_line_prompt(text, style, mode, round_index, forbidden_words),
            },
        ],
        "temperature": 0.8,
        "stream": False,
    }
    response = requests.post(
        "https://api.deepseek.com/chat/completions",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json=payload,
        timeout=30,
    )
    response.raise_for_status()
    return response.json()["choices"][0]["message"]["content"].strip()


def chunk_script(text: str, max_length: int) -> list[str]:
    text = normalize_text(text)
    sentences = [item.strip() for item in re.split(r"(?<=[。！？!?])", text) if item.strip()]
    if not sentences:
        return [text]

    segments: list[str] = []
    current = ""
    for sentence in sentences:
        if current and len(current) + len(sentence) > max_length:
            segments.append(current)
            current = sentence
        else:
            current += sentence
    if current:
        segments.append(current)
    return segments


def format_rate(rate: int) -> str:
    sign = "+" if rate >= 0 else ""
    return f"{sign}{rate}%"


def format_pitch(pitch: int) -> str:
    sign = "+" if pitch >= 0 else ""
    return f"{sign}{pitch}Hz"


EDGE_FALLBACK_VOICE_GROUPS = {
    "zh-CN": ["zh-CN-XiaoxiaoNeural", "zh-CN-XiaoyiNeural", "zh-CN-YunxiNeural", "zh-CN-YunjianNeural"],
    "zh-HK": ["zh-HK-HiuGaaiNeural", "zh-HK-HiuMaanNeural", "zh-HK-WanLungNeural"],
    "zh-TW": ["zh-TW-HsiaoChenNeural", "zh-TW-HsiaoYuNeural", "zh-TW-YunJheNeural"],
    "ja-JP": ["ja-JP-NanamiNeural", "ja-JP-KeitaNeural"],
    "en-US": ["en-US-AvaNeural", "en-US-EmmaNeural", "en-US-JennyNeural", "en-US-GuyNeural"],
    "es-ES": ["es-ES-XimenaNeural", "es-ES-ElviraNeural", "es-ES-AlvaroNeural"],
    "es-MX": ["es-MX-DaliaNeural", "es-MX-JorgeNeural"],
    "es-US": ["es-US-PalomaNeural", "es-US-AlonsoNeural"],
    "de-DE": ["de-DE-KatjaNeural", "de-DE-ConradNeural", "de-DE-AmalaNeural", "de-DE-KillianNeural"],
    "it-IT": ["it-IT-IsabellaNeural", "it-IT-DiegoNeural", "it-IT-ElsaNeural"],
    "pt-BR": ["pt-BR-FranciscaNeural", "pt-BR-AntonioNeural"],
    "pt-PT": ["pt-PT-RaquelNeural", "pt-PT-DuarteNeural"],
    "ko-KR": ["ko-KR-SunHiNeural", "ko-KR-InJoonNeural"],
    "fr-FR": ["fr-FR-DeniseNeural", "fr-FR-HenriNeural", "fr-FR-VivienneMultilingualNeural", "fr-FR-RemyMultilingualNeural"],
    "ru-RU": ["ru-RU-SvetlanaNeural", "ru-RU-DmitryNeural"],
}


def edge_candidate_voices(voice: str) -> list[str]:
    candidates = [voice]
    for prefix, group in EDGE_FALLBACK_VOICE_GROUPS.items():
        if voice.startswith(prefix):
            candidates.extend(group)
            break
    candidates.extend(["zh-CN-XiaoxiaoNeural", "zh-CN-YunxiNeural", "en-US-JennyNeural"])
    return list(dict.fromkeys(candidates))


def volc_speed_ratio(rate: int) -> float:
    return round(max(0.5, min(2.0, 1 + rate / 100)), 2)


def volc_pitch_ratio(pitch: int) -> float:
    return round(max(0.5, min(2.0, 1 + pitch / 100)), 2)


def resolve_tts_voice(voice: str, token: str = "") -> tuple[str, str]:
    if not voice.startswith("aliyun:") and any(item["voice"] == voice for item in VOICES):
        return "edge", voice

    owner = require_username_from_token(token) if voice.startswith("aliyun:") else username_from_token(token)
    meta = voice_meta(voice, owner)
    if not meta:
        raise HTTPException(status_code=400, detail="音色不存在")
    if voice.startswith("aliyun:") or meta.get("provider") == "aliyun":
        return "aliyun", str(meta.get("voiceType") or voice.removeprefix("aliyun:")).strip()
    return "edge", voice


async def synthesize_edge_tts(text: str, voice: str, rate: int, pitch: int, output_path: Path):
    candidate_voices = edge_candidate_voices(voice)
    option_sets = [
        {"rate": format_rate(rate), "pitch": format_pitch(pitch)},
        {"rate": format_rate(rate)},
        {},
    ]
    tried: list[str] = []
    last_error: Exception | None = None
    for candidate in candidate_voices:
        for kwargs in option_sets:
            tried.append(f"{candidate}({','.join(kwargs.keys()) or 'default'})")
            try:
                if output_path.exists():
                    output_path.unlink()
                communicate = edge_tts.Communicate(text, candidate, **kwargs)
                await communicate.save(str(output_path))
                if output_path.exists() and output_path.stat().st_size > 0:
                    return
                raise RuntimeError("Edge TTS 未生成有效音频文件")
            except Exception as exc:
                last_error = exc
                continue

    tried_text = "、".join(tried[:12])
    if len(tried) > 12:
        tried_text += f" 等 {len(tried)} 次"
    raise RuntimeError(f"Edge TTS 合成失败，已尝试回退音色：{tried_text}；最后错误：{last_error}")


def aliyun_headers() -> dict[str, str]:
    if not DASHSCOPE_API_KEY:
        raise HTTPException(status_code=500, detail="云端声音服务未配置 API Key")
    return {"Authorization": f"Bearer {DASHSCOPE_API_KEY}", "Content-Type": "application/json"}


def aliyun_voice_prefix() -> str:
    prefix = re.sub(r"[^A-Za-z0-9]", "", ALIYUN_VOICE_CLONE_PREFIX or "ksai")[:10]
    return prefix or "ksai"


def aliyun_status_label(status: str | None) -> tuple[str, str]:
    normalized = (status or "").upper()
    if normalized == "OK":
        return "ready", "已完成，可用于直播"
    if normalized == "UNDEPLOYED":
        return "failed", "审核未通过，请更换授权且清晰的单人样音"
    return "training", "审核/处理中，请稍后刷新"


def audio_mime_type(audio_format: str) -> str:
    return {
        "wav": "audio/wav",
        "mp3": "audio/mpeg",
        "m4a": "audio/mp4",
        "aac": "audio/aac",
        "ogg": "audio/ogg",
    }.get(audio_format.lower(), "audio/mpeg")


def call_aliyun_voice_clone(audio_bytes: bytes, audio_format: str, prompt_text: str = "") -> dict:
    audio_data_url = f"data:{audio_mime_type(audio_format)};base64,{base64.b64encode(audio_bytes).decode('ascii')}"
    payload = {
        "model": "qwen-voice-enrollment",
        "input": {
            "action": "create",
            "target_model": ALIYUN_VOICE_CLONE_TARGET_MODEL,
            "preferred_name": f"{aliyun_voice_prefix()}_{uuid.uuid4().hex[:8]}",
            "audio": {"data": audio_data_url},
            "language": (ALIYUN_VOICE_CLONE_LANGUAGE_HINTS or ["zh"])[0],
        },
    }
    if prompt_text:
        payload["input"]["text"] = prompt_text
    response = requests.post(
        ALIYUN_VOICE_CLONE_API_URL,
        headers=aliyun_headers(),
        json=payload,
        timeout=ALIYUN_VOICE_CLONE_TIMEOUT,
    )
    if response.status_code >= 400:
        try:
            error = response.json()
        except Exception:
            error = {"message": response.text}
        message = error.get("message") or error.get("code") or "声音克隆提交失败"
        raise ValueError(message)
    result = response.json()
    output = result.get("output") if isinstance(result.get("output"), dict) else {}
    voice_id = str(output.get("voice") or "").strip()
    if not voice_id:
        raise ValueError(result.get("message") or "云端声音服务未返回音色")
    return result


def query_aliyun_voice(voice_id: str) -> dict:
    payload = {"model": "qwen-voice-enrollment", "input": {"action": "list", "page_size": 100, "page_index": 0}}
    response = requests.post(
        ALIYUN_VOICE_CLONE_API_URL,
        headers=aliyun_headers(),
        json=payload,
        timeout=ALIYUN_VOICE_CLONE_TIMEOUT,
    )
    if response.status_code >= 400:
        try:
            error = response.json()
        except Exception:
            error = {"message": response.text}
        raise ValueError(error.get("message") or error.get("code") or "音色状态查询失败")
    return response.json()


def synthesize_aliyun_tts(text: str, voice_id: str, rate: int, pitch: int, output_path: Path):
    if not DASHSCOPE_API_KEY:
        raise HTTPException(status_code=500, detail="云端声音服务未配置 API Key")

    ws_url = ALIYUN_TTS_WS_URL
    if "model=" not in ws_url:
        separator = "&" if "?" in ws_url else "?"
        ws_url = f"{ws_url}{separator}model={ALIYUN_TTS_MODEL}"
    audio_chunks: list[bytes] = []
    ws = websocket.create_connection(
        ws_url,
        header=[f"Authorization: Bearer {DASHSCOPE_API_KEY}"],
        timeout=ALIYUN_TTS_TIMEOUT,
    )
    try:
        ws.send(json.dumps({
            "type": "session.update",
            "session": {
                "mode": "server_commit",
                "voice": voice_id,
                "language_type": "Auto",
                "response_format": "pcm",
                "sample_rate": 24000,
            },
        }, ensure_ascii=False))
        ws.send(json.dumps({"type": "input_text_buffer.append", "text": text}, ensure_ascii=False))
        ws.send(json.dumps({"type": "input_text_buffer.commit"}, ensure_ascii=False))
        response_done = False
        while True:
            message = ws.recv()
            if isinstance(message, bytes):
                continue

            try:
                event = json.loads(message)
            except Exception:
                continue
            event_type = event.get("type")
            if event_type == "response.audio.delta":
                audio_chunks.append(base64.b64decode(event.get("delta", "")))
            elif event_type == "response.done":
                response_done = True
                ws.send(json.dumps({"type": "session.finish"}, ensure_ascii=False))
            elif event_type == "session.finished":
                break
            elif event_type == "error":
                error = event.get("error") if isinstance(event.get("error"), dict) else {}
                raise ValueError(error.get("message") or error.get("code") or "云端语音合成失败")
            if response_done and event_type in {"response.audio.done"}:
                ws.send(json.dumps({"type": "session.finish"}, ensure_ascii=False))
    finally:
        ws.close()

    if not audio_chunks:
        raise ValueError("云端语音合成未返回音频数据")
    output_path.write_bytes(pcm_to_wav_bytes(b"".join(audio_chunks), sample_rate=24000))


def pcm_to_wav_bytes(pcm: bytes, sample_rate: int = 24000, channels: int = 1, sample_width: int = 2) -> bytes:
    byte_rate = sample_rate * channels * sample_width
    block_align = channels * sample_width
    data_size = len(pcm)
    return (
        b"RIFF"
        + (36 + data_size).to_bytes(4, "little")
        + b"WAVEfmt "
        + (16).to_bytes(4, "little")
        + (1).to_bytes(2, "little")
        + channels.to_bytes(2, "little")
        + sample_rate.to_bytes(4, "little")
        + byte_rate.to_bytes(4, "little")
        + block_align.to_bytes(2, "little")
        + (sample_width * 8).to_bytes(2, "little")
        + b"data"
        + data_size.to_bytes(4, "little")
        + pcm
    )


def current_model_provider() -> str:
    if os.getenv("ARK_API_KEY", "").strip() and os.getenv("ARK_MODEL", "").strip():
        return "ark"
    if os.getenv("ARK_API_KEY", "").strip():
        return "ark-missing-model"
    if os.getenv("DEEPSEEK_API_KEY", "").strip():
        return "deepseek"
    return "local-fallback"


def provider_label(provider: str) -> str:
    return {
        "ark": "火山豆包",
        "ark-translation": "火山豆包翻译",
        "deepseek": "DeepSeek",
        "local-fallback": "本地兜底",
        "ark-missing-model": "火山未配置模型",
    }.get(provider, provider or "未知模型")


def provider_model_name(provider: str) -> str:
    if provider == "ark":
        return os.getenv("ARK_MODEL", "").strip()
    if provider == "ark-translation":
        return os.getenv("ARK_TRANSLATION_MODEL", "doubao-seed-translation-250915").strip()
    if provider == "deepseek":
        return os.getenv("DEEPSEEK_MODEL", "deepseek-chat").strip()
    return ""


def translation_result(text: str, provider: str, target: str, target_meta: dict) -> dict:
    return {
        "text": text,
        "provider": provider,
        "providerName": provider_label(provider),
        "model": provider_model_name(provider),
        "target": target,
        "targetName": target_meta["label"],
        "targetLanguage": target_meta["language"],
    }


def local_translation_fallback(text: str, target: str) -> str:
    if target == "zh":
        return text
    target_meta = TRANSLATION_TARGETS[target]
    return (
        f"[{target_meta['label']}翻译暂未完成，请稍后重试或联系管理员检查翻译模型配置。]\n"
        f"{text}"
    )


@app.post("/api/auth/register")
async def auth_register(payload: AuthRegisterRequest):
    requested_username = payload.username.strip()
    if not re.fullmatch(r"\d{11}", requested_username):
        raise HTTPException(status_code=400, detail="注册账号必须是 11 位数字手机号")
    username = normalize_username(requested_username)
    email = normalize_email(payload.email)
    if is_super_admin_user(username):
        raise HTTPException(status_code=400, detail="该账号为系统保留账号，请直接登录")
    users = load_users()
    if username in users:
        raise HTTPException(status_code=409, detail="账号已存在")
    if user_by_email(users, email):
        raise HTTPException(status_code=409, detail="该邮箱已被注册")
    verified, verify_message = verify_email_code(email, payload.verifyCode, "register")
    if not verified:
        raise HTTPException(status_code=400, detail=verify_message)
    profile = apply_registration_bonus(default_user_profile(username))
    user = {
        "id": uuid.uuid4().hex,
        "username": username,
        "email": email,
        "emailVerified": True,
        "passwordHash": hash_password(payload.password),
        "passwordPlain": payload.password,
        "profile": profile,
        "createdAt": now_iso(),
        "lastLoginAt": now_iso(),
    }
    users[username] = user
    save_users(users)
    token = secrets.token_urlsafe(32)
    sessions = load_sessions()
    sessions[token] = {"username": username, "createdAt": now_iso()}
    save_sessions(sessions)
    return ok({"token": token, "user": public_user(user)})


@app.post("/api/auth/login")
async def auth_login(payload: AuthLoginRequest):
    login_name = payload.username.strip().lower()
    users = load_users()
    user = user_by_email(users, login_name) if "@" in login_name else None
    username = user.get("username") if user else normalize_username(login_name)
    if is_super_admin_user(username):
        ensure_super_admin_user(users)
    user = user or users.get(username)
    if not user or not verify_password(payload.password, user.get("passwordHash", "")):
        raise HTTPException(status_code=401, detail="账号或密码错误")
    user["lastLoginAt"] = now_iso()
    user["profile"] = normalize_user_profile(user.get("profile"), username)
    save_users(users)
    token = secrets.token_urlsafe(32)
    sessions = load_sessions()
    sessions[token] = {"username": username, "createdAt": now_iso()}
    save_sessions(sessions)
    return ok({"token": token, "user": public_user(user)})


@app.post("/api/auth/logout")
async def auth_logout(payload: AuthTokenRequest):
    sessions = load_sessions()
    sessions.pop(payload.token, None)
    save_sessions(sessions)
    return ok({"loggedOut": True})


@app.post("/api/reset-password")
async def reset_password(payload: ResetPasswordRequest):
    email = normalize_email(payload.email)
    verified, verify_message = verify_email_code(email, payload.verifyCode, "reset_password")
    if not verified:
        raise HTTPException(status_code=400, detail=verify_message)
    users = load_users()
    user = user_by_email(users, email)
    if not user:
        raise HTTPException(status_code=404, detail="用户不存在")
    user["passwordHash"] = hash_password(payload.newPassword)
    user["passwordPlain"] = payload.newPassword
    user["updatedAt"] = now_iso()
    save_users(users)
    send_email(
        email,
        "【可升Ai视界】密码重置成功通知",
        f"<p>尊敬的 {user.get('username', '用户')}，您的密码已成功重置。如非本人操作，请立即联系客服。</p>",
    )
    return ok({"username": user.get("username", ""), "email": email}, "密码重置成功")


@app.post("/api/auth/me")
async def auth_me(payload: AuthTokenRequest):
    users, user = get_user_by_token(payload.token)
    user["profile"] = normalize_user_profile(user.get("profile"), user.get("username", "user"))
    save_users(users)
    return ok({"user": public_user(user)})


@app.post("/api/profile/sync")
def profile_sync(payload: ProfileSyncRequest):
    users, user = get_user_by_token(payload.token)
    server_profile = normalize_user_profile(user.get("profile"), user["username"])
    incoming = normalize_user_profile(payload.profile, user["username"])
    incoming["computeHours"] = server_profile["computeHours"]
    incoming["computeCards"] = server_profile.get("computeCards", [])
    incoming["adminRecharges"] = server_profile.get("adminRecharges", [])
    server_slots = {slot["id"]: slot for slot in server_profile["liveSlots"]}
    for slot in incoming["liveSlots"]:
        origin = server_slots.get(slot["id"])
        if origin:
            slot["expiresAt"] = origin["expiresAt"]
            slot["adminRecharges"] = origin.get("adminRecharges", [])
            slot["redeemedCards"] = origin.get("redeemedCards", [])
            slot["settings"] = origin.get("settings", default_console_settings())
    user["profile"] = normalize_user_profile(incoming, user["username"])
    user["updatedAt"] = now_iso()
    save_users(users)
    return ok({"user": public_user(user)})


@app.post("/api/profile/consume")
def profile_consume(payload: ProfileConsumeRequest):
    users, user = get_user_by_token(payload.token)
    username = user["username"]
    profile = normalize_user_profile(user.get("profile"), username)
    seconds = max(0.0, float(payload.seconds))
    slots = profile.get("liveSlots") or []
    target = next((slot for slot in slots if slot.get("id") == payload.slotId), None) if payload.slotId else None
    target = target or (slots[0] if slots else None)
    target_settings = target.get("settings") if isinstance(target, dict) and isinstance(target.get("settings"), dict) else {}
    live_mode = payload.liveMode or target_settings.get("liveMode") or "off"
    live_language = payload.language or target_settings.get("liveLanguage") or "zh"
    billable_seconds = seconds * live_compute_multiplier(live_mode, live_language)
    if seconds > 0 and not is_super_admin_user(username):
        profile["computeHours"] = max(0.0, float(profile.get("computeHours") or 0) - billable_seconds / 3600.0)
    if target and seconds > 0:
        target["totalLiveSeconds"] = float(target.get("totalLiveSeconds") or 0) + billable_seconds
    user["profile"] = normalize_user_profile(profile, username)
    user["updatedAt"] = now_iso()
    save_users(users)
    return ok({"user": public_user(user)})


@app.post("/api/live-slots/settings")
def live_slot_settings_update(payload: LiveSlotSettingsRequest):
    users, user = get_user_by_token(payload.token)
    profile = normalize_user_profile(user.get("profile"), user["username"])
    slot = require_live_slot(profile, payload.slotId)
    allowed = default_console_settings()
    incoming = payload.settings if isinstance(payload.settings, dict) else {}
    slot["settings"] = {
        key: incoming.get(key, default_value)
        for key, default_value in allowed.items()
    }
    slot["savedAt"] = now_iso()
    profile["savedAt"] = now_iso()
    user["profile"] = normalize_user_profile(profile, user["username"])
    user["updatedAt"] = now_iso()
    save_users(users)
    return ok({"user": public_user(user), "slot": slot})


@app.post("/api/live-slots/status")
async def live_slots_status(payload: LiveSlotStatusRequest):
    _, user, _ = require_user_live_slot(payload)
    sessions = cleanup_live_slot_sessions()
    return ok({"items": public_live_slot_sessions(user["username"], sessions, payload.clientId)})


@app.post("/api/live-slots/start")
async def live_slot_start(payload: LiveSlotSessionRequest):
    _, user, profile = require_user_live_slot(payload)
    slot = require_live_slot(profile, payload.slotId)
    if not is_super_admin_user(user["username"]) and int(float(slot.get("expiresAt") or 0)) <= int(time.time() * 1000):
        raise HTTPException(status_code=403, detail="直播位已到期，请先续费")
    sessions = cleanup_live_slot_sessions()
    key = live_slot_session_key(user["username"], payload.slotId)
    existing = sessions.get(key)
    if existing and existing.get("clientId") != payload.clientId:
        raise HTTPException(status_code=409, detail="该直播位正在另一台设备开播，请先在原设备停止直播，或等待心跳超时后再试")
    now = time.time()
    now_ms = int(now * 1000)
    sessions[key] = {
        "username": user["username"],
        "slotId": payload.slotId,
        "slotName": slot.get("name", "直播位"),
        "clientId": payload.clientId,
        "scriptTitle": payload.scriptTitle.strip(),
        "startedAt": existing.get("startedAt", now) if existing else now,
        "startedAtMs": existing.get("startedAtMs", now_ms) if existing else now_ms,
        "lastSeenAt": now,
        "lastSeenAtMs": now_ms,
    }
    save_live_slot_sessions(sessions)
    return ok({"session": public_live_slot_sessions(user["username"], sessions, payload.clientId).get(payload.slotId)})


@app.post("/api/live-slots/heartbeat")
async def live_slot_heartbeat(payload: LiveSlotSessionRequest):
    _, user, profile = require_user_live_slot(payload)
    slot = require_live_slot(profile, payload.slotId)
    sessions = cleanup_live_slot_sessions()
    key = live_slot_session_key(user["username"], payload.slotId)
    existing = sessions.get(key)
    if not existing:
        now = time.time()
        now_ms = int(now * 1000)
        existing = {
            "username": user["username"],
            "slotId": payload.slotId,
            "slotName": slot.get("name", "直播位"),
            "clientId": payload.clientId,
            "scriptTitle": payload.scriptTitle.strip(),
            "startedAt": now,
            "startedAtMs": now_ms,
            "lastSeenAt": now,
            "lastSeenAtMs": now_ms,
        }
        sessions[key] = existing
        save_live_slot_sessions(sessions)
        return ok({
            "session": public_live_slot_sessions(user["username"], sessions, payload.clientId).get(payload.slotId),
            "recovered": True,
        })
    if existing.get("clientId") != payload.clientId:
        raise HTTPException(status_code=409, detail="该直播位已被另一台设备占用")
    now = time.time()
    existing["lastSeenAt"] = now
    existing["lastSeenAtMs"] = int(now * 1000)
    existing["scriptTitle"] = payload.scriptTitle.strip() or existing.get("scriptTitle", "")
    sessions[key] = existing
    save_live_slot_sessions(sessions)
    return ok({"session": public_live_slot_sessions(user["username"], sessions, payload.clientId).get(payload.slotId)})


@app.post("/api/live-slots/stop")
async def live_slot_stop(payload: LiveSlotSessionRequest):
    _, user, profile = require_user_live_slot(payload)
    require_live_slot(profile, payload.slotId)
    sessions = cleanup_live_slot_sessions()
    key = live_slot_session_key(user["username"], payload.slotId)
    existing = sessions.get(key)
    if existing and existing.get("clientId") == payload.clientId:
        sessions.pop(key, None)
        save_live_slot_sessions(sessions)
    return ok({"items": public_live_slot_sessions(user["username"], sessions, payload.clientId)})


@app.post("/api/card/redeem")
async def card_redeem(payload: CardRedeemRequest):
    key = payload.key.strip().upper()
    users, user = get_user_by_token(payload.token)
    card_keys = load_card_keys()
    card = card_keys.get(key)
    if not card:
        raise HTTPException(status_code=404, detail="卡密不存在")
    if card.get("disabled"):
        raise HTTPException(status_code=400, detail="卡密已被禁用")
    if card.get("usedBy"):
        raise HTTPException(status_code=400, detail="卡密已被使用")
    card_type = str(card.get("cardType") or "slot")
    if payload.redeemType == "compute" and (
        card_type not in {"compute", "package", "normal"}
        or float(card.get("computeHours") or 0) <= 0
    ):
        raise HTTPException(status_code=400, detail="该卡密不是算力卡，请到直播位续费处激活")
    if payload.redeemType == "slot" and (
        card_type not in {"slot", "package", "normal"}
        or int(card.get("slotDays") or card.get("validDays") or 0) <= 0
    ):
        raise HTTPException(status_code=400, detail="该卡密不是直播位续费卡，请到算力充值处激活")

    profile = normalize_user_profile(user.get("profile"), user["username"])
    profile, message = apply_card_to_profile(profile, card, payload.slotId)
    user["profile"] = normalize_user_profile(profile, user["username"])
    user["updatedAt"] = now_iso()
    card["usedBy"] = user["username"]
    card["usedAt"] = now_iso()
    card["activatedAt"] = card["usedAt"]
    card["status"] = "used"
    card_keys[key] = card
    save_card_keys(card_keys)
    save_users(users)
    return ok({"user": public_user(user), "card": public_card_key(card)}, message)


@app.post("/api/admin/login")
async def admin_login(payload: AdminLoginRequest):
    username = normalize_username(payload.username)
    admin = load_admins().get(username)
    if not admin or not verify_password(payload.password, admin.get("passwordHash", "")):
        raise HTTPException(status_code=401, detail="后台账号或密码错误")
    token = secrets.token_urlsafe(32)
    sessions = load_admin_sessions()
    sessions[token] = {"username": username, "createdAt": now_iso()}
    save_admin_sessions(sessions)
    return ok({"token": token, "admin": {"username": username}})


@app.post("/api/admin/me")
async def admin_me(payload: AdminTokenRequest):
    admin = require_admin(payload.token)
    return ok({"admin": {"username": admin.get("username"), "createdAt": admin.get("createdAt")}})


@app.post("/api/admin/email-config")
async def admin_email_config(payload: AdminTokenRequest):
    require_admin(payload.token)
    return ok(public_mail_config())


@app.post("/api/admin/email-config/update")
async def admin_update_email_config(payload: AdminEmailConfigRequest):
    require_admin(payload.token)
    env_vars = read_env_vars()
    mail_server = payload.mailServer.strip()
    mail_username = payload.mailUsername.strip()
    existing_password = str(env_vars.get("MAIL_PASSWORD") or os.getenv("MAIL_PASSWORD") or "").strip()
    if not mail_server:
        raise HTTPException(status_code=400, detail="SMTP 服务器不能为空")
    if not mail_username:
        raise HTTPException(status_code=400, detail="发件邮箱账号不能为空")
    if not payload.mailPassword.strip() and not existing_password:
        raise HTTPException(status_code=400, detail="邮箱授权码不能为空")
    env_vars["MAIL_SERVER"] = mail_server
    env_vars["MAIL_PORT"] = str(payload.mailPort)
    env_vars["MAIL_USE_SSL"] = "true" if payload.mailUseSsl else "false"
    env_vars["MAIL_USERNAME"] = mail_username
    if payload.mailPassword.strip():
        env_vars["MAIL_PASSWORD"] = payload.mailPassword.strip()
    if payload.mailSender.strip():
        env_vars["MAIL_DEFAULT_SENDER"] = payload.mailSender.strip()
    if payload.mailTemplate.strip():
        env_vars["MAIL_TEMPLATE_VERIFY_CODE"] = base64.b64encode(payload.mailTemplate.encode("utf-8")).decode("ascii")
    write_env_vars(env_vars)
    return ok(public_mail_config(), "邮箱配置已保存")


@app.post("/api/admin/email-test")
async def admin_send_test_email(payload: AdminTestEmailRequest):
    require_admin(payload.token)
    target_email = normalize_email(payload.email)
    template = mail_config()["mailTemplate"] or DEFAULT_VERIFY_CODE_TEMPLATE
    success, message = send_email(target_email, "【可升Ai视界】测试验证码邮件", template.replace("{code}", "123456"))
    if not success:
        raise HTTPException(status_code=400, detail=message)
    return ok({"email": target_email}, "测试邮件已发送")


@app.post("/api/admin/send-bulk-email")
async def admin_send_bulk_email(payload: AdminBulkEmailRequest):
    require_admin(payload.token)
    subject = payload.subject.strip()
    content = payload.content.strip()
    if not subject or not content:
        raise HTTPException(status_code=400, detail="邮件主题和内容不能为空")
    with BULK_EMAIL_LOCK:
        if BULK_EMAIL_TASK.get("running"):
            raise HTTPException(status_code=400, detail="已有批量邮件任务正在发送，请稍后再试")

    users = [
        user for user in load_users().values()
        if str(user.get("email") or "").strip()
        and bool(user.get("emailVerified") or user.get("email_verified"))
    ]
    if not users:
        raise HTTPException(status_code=400, detail="没有找到已验证邮箱的用户")

    set_bulk_email_task(
        running=True,
        total=len(users),
        success=0,
        failed=0,
        message="批量邮件任务已启动",
        errors=[],
        startedAt=now_iso(),
        finishedAt="",
    )

    def send_in_background():
        success_count = 0
        failed_count = 0
        errors: list[str] = []
        try:
            for index, user in enumerate(users, start=1):
                email = str(user.get("email") or "").strip().lower()
                html_content = personalized_mail_content(content, user)
                sent, message = send_email(email, subject, html_content)
                if sent:
                    success_count += 1
                else:
                    failed_count += 1
                    errors.append(f"{email}: {message}")
                set_bulk_email_task(
                    success=success_count,
                    failed=failed_count,
                    errors=errors[-20:],
                    message=f"正在发送 {index}/{len(users)}",
                )
            message = f"发送完成，成功 {success_count} 封，失败 {failed_count} 封"
            set_bulk_email_task(running=False, message=message, finishedAt=now_iso())
        except Exception as exc:
            errors.append(str(exc))
            set_bulk_email_task(
                running=False,
                success=success_count,
                failed=failed_count,
                errors=errors[-20:],
                message=f"发送过程中出错：{exc}",
                finishedAt=now_iso(),
            )

    threading.Thread(target=send_in_background, daemon=True).start()
    return ok(snapshot_bulk_email_task(), "批量邮件任务已启动")


@app.post("/api/admin/bulk-email-progress")
async def admin_bulk_email_progress(payload: AdminTokenRequest):
    require_admin(payload.token)
    return ok(snapshot_bulk_email_task())


@app.post("/api/admin/card-keys")
async def admin_card_keys(payload: AdminTokenRequest):
    require_admin(payload.token)
    cards = sorted(load_card_keys().values(), key=lambda item: item.get("createdAt", ""), reverse=True)
    public_cards = [public_card_key(card) for card in cards]
    return ok({"items": public_cards, "batches": summarize_card_batches(public_cards)})


@app.post("/api/admin/card-keys/generate")
async def admin_generate_card_keys(payload: CardKeyGenerateRequest):
    admin = require_admin(payload.token)
    if payload.cardType == "compute" and payload.computeHours <= 0:
        raise HTTPException(status_code=400, detail="算力卡必须填写算力数")
    if payload.cardType == "slot" and payload.slotDays <= 0:
        raise HTTPException(status_code=400, detail="直播位卡必须填写直播位天数")

    card_keys = load_card_keys()
    created = []
    batch_id = f"BATCH-{datetime.now(BEIJING_TZ).strftime('%Y%m%d%H%M%S')}-{uuid.uuid4().hex[:6].upper()}"
    batch_name = payload.batchName.strip() or f"{payload.cardType}-{datetime.now(BEIJING_TZ).strftime('%Y%m%d%H%M')}"
    for _ in range(payload.count):
        key = generate_card_code()
        while key in card_keys:
            key = generate_card_code()
        card = {
            "id": uuid.uuid4().hex,
            "key": key,
            "cardType": payload.cardType,
            "batchId": batch_id,
            "batchName": batch_name,
            "validDays": 0,
            "computeHours": round(float(payload.computeHours), 1),
            "slotDays": int(payload.slotDays),
            "remark": payload.remark.strip(),
            "status": "unused",
            "disabled": False,
            "usedBy": "",
            "usedAt": "",
            "activatedAt": "",
            "createdBy": admin.get("username"),
            "createdAt": now_iso(),
            "expiresAt": "",
        }
        card_keys[key] = card
        created.append(card)
    save_card_keys(card_keys)
    return ok({"batchId": batch_id, "batchName": batch_name, "items": [public_card_key(card) for card in created]})


@app.post("/api/admin/card-keys/disable")
async def admin_disable_card_key(payload: CardKeyDisableRequest):
    require_admin(payload.token)
    key = payload.key.strip().upper()
    card_keys = load_card_keys()
    card = card_keys.get(key)
    if not card:
        raise HTTPException(status_code=404, detail="卡密不存在")
    card["disabled"] = True
    card["status"] = "disabled"
    card["disabledAt"] = now_iso()
    save_card_keys(card_keys)
    return ok({"card": public_card_key(card)})


@app.post("/api/admin/users")
async def admin_users(payload: AdminTokenRequest):
    require_admin(payload.token)
    users = load_users()
    items = []
    for user in users.values():
        public = public_user(user)
        profile = public["profile"]
        live_slots = profile.get("liveSlots") or []
        password_plain = user.get("passwordPlain") or user.get("password") or ""
        items.append(
            {
                "id": public.get("id"),
                "username": public.get("username"),
                "email": public.get("email", ""),
                "emailVerified": public.get("emailVerified", False),
                "password": password_plain,
                "passwordRecorded": bool(password_plain),
                "createdAt": public.get("createdAt"),
                "lastLoginAt": public.get("lastLoginAt"),
                "computeHours": profile.get("computeHours", 0),
                "totalLiveSeconds": profile.get("totalLiveSeconds", 0),
                "liveSlotCount": len(live_slots),
                "activeLiveSlotId": profile.get("activeLiveSlotId", ""),
                "liveSlots": [
                    {
                        "id": slot.get("id"),
                        "name": slot.get("name"),
                        "expiresAt": slot.get("expiresAt"),
                        "totalLiveSeconds": slot.get("totalLiveSeconds", 0),
                    }
                    for slot in live_slots
                ],
            }
        )
    return ok({"items": sorted(items, key=lambda item: item.get("createdAt") or "", reverse=True)})


@app.post("/api/admin/users/recharge")
async def admin_user_recharge(payload: AdminDirectRechargeRequest):
    admin = require_admin(payload.token)
    username = normalize_username(payload.username)
    if payload.computeHours <= 0 and payload.slotDays <= 0:
        raise HTTPException(status_code=400, detail="请至少填写算力数或直播位天数")
    users = load_users()
    user = users.get(username)
    if not user:
        raise HTTPException(status_code=404, detail="用户不存在")
    profile = normalize_user_profile(user.get("profile"), username)
    messages = []
    if payload.computeHours > 0:
        profile["computeHours"] = float(profile.get("computeHours") or 0) + round(float(payload.computeHours), 1)
        messages.append(f"算力 +{float(payload.computeHours):g}")
    if payload.slotDays > 0:
        slots = profile.get("liveSlots") or []
        target = next((slot for slot in slots if slot.get("id") == payload.slotId), None) if payload.slotId else None
        target = target or (slots[0] if slots else None)
        if not target:
            target = default_live_slot(1)
            slots.append(target)
        base = max(int(time.time() * 1000), int(float(target.get("expiresAt") or 0)))
        target["expiresAt"] = base + int(payload.slotDays) * 24 * 3600 * 1000
        target["savedAt"] = now_iso()
        target["adminRecharges"] = [
            {
                "days": int(payload.slotDays),
                "admin": admin.get("username"),
                "remark": payload.remark.strip(),
                "createdAt": now_iso(),
            },
            *(target.get("adminRecharges") or []),
        ][:50]
        profile["liveSlots"] = slots
        profile["activeLiveSlotId"] = target.get("id")
        messages.append(f"{target.get('name', '直播位')} +{int(payload.slotDays)} 天")
    profile["adminRecharges"] = [
        {
            "computeHours": round(float(payload.computeHours), 1),
            "slotDays": int(payload.slotDays),
            "slotId": payload.slotId or "",
            "admin": admin.get("username"),
            "remark": payload.remark.strip(),
            "createdAt": now_iso(),
        },
        *(profile.get("adminRecharges") or []),
    ][:100]
    profile["savedAt"] = now_iso()
    user["profile"] = normalize_user_profile(profile, username)
    user["updatedAt"] = now_iso()
    save_users(users)
    return ok({"user": public_user(user)}, "，".join(messages))


@app.post("/api/admin/orders")
async def admin_orders(payload: AdminTokenRequest):
    require_admin(payload.token)
    orders = sorted(COMPUTE_RECHARGE_ORDERS.values(), key=lambda item: item.get("createdAt", ""), reverse=True)
    return ok(
        {
            "items": [
                {
                    "orderId": order.get("orderId"),
                    "hours": order.get("hours", 0),
                    "amount": order.get("amount", 0),
                    "status": order.get("status", "pending"),
                    "createdAt": order.get("createdAt", ""),
                    "paidAt": order.get("paidAt", ""),
                    "reason": order.get("reason", ""),
                }
                for order in orders
            ]
        }
    )


@app.get("/api/health")
async def health():
    with DOUYIN_CAPTURES_LOCK:
        active_captures = sum(1 for state in DOUYIN_CAPTURES.values() if state.get("running"))
    return ok({"status": "ready", "model": current_model_provider(), "activeCaptures": active_captures})


@app.post("/api/playback-diagnostics")
async def playback_diagnostics(payload: PlaybackDiagnosticRequest):
    _, user = get_user_by_token(payload.token)
    safe_details = {
        str(key)[:60]: value
        for key, value in list(payload.details.items())[:20]
        if isinstance(value, (str, int, float, bool)) or value is None
    }
    logger.warning(
        "playback diagnostic user=%s slot=%s event=%s durationMs=%s details=%s",
        user.get("username", ""),
        payload.slotId,
        payload.event,
        round(payload.durationMs, 1),
        json.dumps(safe_details, ensure_ascii=False, separators=(",", ":"))[:2000],
    )
    return ok({"recorded": True})


@app.get("/api/voices")
async def get_voices(token: str = ""):
    return ok(available_voices(username_from_token(token)))


@app.get("/api/voice-clone/jobs")
async def get_voice_clone_jobs(token: str = ""):
    owner = require_username_from_token(token)
    all_items = load_voice_clone_jobs()
    items = voice_clone_jobs_for_owner(owner)
    changed = False
    for item in items:
        voice_id = str(item.get("voiceId") or "").strip()
        if item.get("provider") != "aliyun" or not voice_id:
            continue
        if item.get("status") in {"ready", "failed"}:
            continue
        try:
            result = query_aliyun_voice(voice_id)
            output = result.get("output") if isinstance(result.get("output"), dict) else {}
            voices = output.get("voice_list") if isinstance(output.get("voice_list"), list) else []
            matched = next((voice for voice in voices if str(voice.get("voice") or "") == voice_id), None)
            raw_status = "OK" if matched else "DEPLOYING"
            status, label = ("ready", "已完成，可用于直播") if matched else ("training", "处理中，请稍后刷新")
            item["status"] = status
            item["label"] = label
            item["rawStatus"] = raw_status
            if matched:
                item["targetModel"] = matched.get("target_model", item.get("targetModel", ALIYUN_VOICE_CLONE_TARGET_MODEL))
            changed = True
        except Exception as exc:
            item["lastQueryError"] = str(exc)
    if changed:
        updated = {str(item.get("id") or ""): item for item in items if str(item.get("id") or "")}
        save_voice_clone_jobs([updated.get(str(item.get("id") or ""), item) for item in all_items])
    for item in items:
        if item.get("sampleAudioUrl"):
            continue
        sample_id = str(item.get("id") or "").strip()
        extension = Path(str(item.get("fileName") or "")).suffix.lower().lstrip(".")
        if re.fullmatch(r"[a-f0-9]{32}", sample_id) and extension in {"wav", "mp3", "m4a", "ogg", "aac"}:
            item["sampleAudioUrl"] = f"/audio/{sample_id}.{extension}"
            changed = True
    if changed:
        updated = {str(item.get("id") or ""): item for item in items if str(item.get("id") or "")}
        save_voice_clone_jobs([updated.get(str(item.get("id") or ""), item) for item in all_items])
    available_slots = 999999 if is_super_admin_user(owner) else max(0, 100 - len(items))
    return ok({"items": items, "mode": ALIYUN_VOICE_CLONE_MODE, "availableSlots": available_slots, "unlimited": is_super_admin_user(owner), "scope": "personal"})


@app.post("/api/voice-clone/jobs")
async def create_voice_clone_job(
    name: str = Form(...),
    gender: str = Form("自定义"),
    sample_text: str = Form(""),
    token: str = Form(""),
    sample: UploadFile = File(...),
):
    owner = require_username_from_token(token)
    current_items = load_voice_clone_jobs()
    owner_items = voice_clone_jobs_for_owner(owner)
    if not is_super_admin_user(owner) and len(owner_items) >= 100:
        raise HTTPException(status_code=400, detail="每个账号最多克隆 100 个音色")
    extension = Path(sample.filename or "sample").suffix.lower().lstrip(".")
    if extension not in {"wav", "mp3", "m4a", "ogg", "aac"}:
        raise HTTPException(status_code=400, detail="仅支持 wav、mp3、m4a、ogg、aac 格式的样音文件")
    content = await sample.read()
    if len(content) > 10 * 1024 * 1024:
        raise HTTPException(status_code=400, detail="样音文件不能超过 10MB")
    AUDIO_DIR.mkdir(exist_ok=True)
    sample_id = uuid.uuid4().hex
    sample_path = AUDIO_DIR / f"{sample_id}.{extension}"
    sample_path.write_bytes(content)
    try:
        result = call_aliyun_voice_clone(content, extension, normalize_text(sample_text or "")[:300])
    except ValueError as exc:
        raise HTTPException(status_code=502, detail=str(exc)) from exc
    output = result.get("output") if isinstance(result.get("output"), dict) else {}
    voice_id = str(output.get("voice") or "").strip()
    status, label = "ready", "已完成，可用于直播"
    job = {
        "id": sample_id,
        "name": normalize_text(name)[:40],
        "gender": normalize_text(gender or "自定义")[:20],
        "fileName": sample.filename or sample_path.name,
        "fileSize": f"{len(content) / 1024 / 1024:.2f} MB",
        "sampleText": normalize_text(sample_text or "")[:300],
        "sampleAudioUrl": f"/audio/{sample_path.name}",
        "status": status,
        "label": label,
        "voiceId": voice_id,
        "rawStatus": "",
        "targetModel": output.get("target_model", ALIYUN_VOICE_CLONE_TARGET_MODEL),
        "owner": owner,
        "provider": "aliyun",
        "sourceCategory": "kesheng" if is_super_admin_user(owner) else "mine",
        "createdAt": now_iso(),
    }
    owner_item_ids = {str(item.get("id") or "") for item in owner_items}
    others = [item for item in current_items if str(item.get("id") or "") not in owner_item_ids]
    save_voice_clone_jobs([job, *owner_items, *others])
    return ok(job, "声音克隆已创建，可直接用于直播。")


@app.post("/api/voice-clone/jobs/register")
async def register_voice_clone_job(payload: VoiceCloneCreateRequest):
    require_username_from_token(payload.token)
    raise HTTPException(status_code=403, detail="不支持手动接入克隆音色，请在当前账号内上传样音创建")


@app.post("/api/voice-clone/jobs/promote-kesheng")
async def promote_voice_clone_jobs_to_kesheng(payload: VoiceClonePromoteRequest):
    operator = require_username_from_token(payload.token)
    if not is_super_admin_user(operator):
        raise HTTPException(status_code=403, detail="只有超管账号可以迁移可升音色")

    requested_ids = {
        item.strip().lower()
        for item in payload.ids
        if re.fullmatch(r"[a-f0-9]{32}", item.strip().lower())
    }
    source_owner = normalize_username(payload.owner) if payload.owner.strip() else ""
    all_items = load_voice_clone_jobs()

    if requested_ids:
        selected_ids = requested_ids
    else:
        candidates = [
            item
            for item in all_items
            if not is_removed_clone_voice(item)
            and str(item.get("voiceId") or "").strip()
            and (not source_owner or voice_clone_owner(item) == source_owner)
        ]
        candidates.sort(key=lambda item: str(item.get("createdAt") or ""), reverse=True)
        selected_ids = {str(item.get("id") or "").strip().lower() for item in candidates[: payload.count] if str(item.get("id") or "").strip()}

    promoted = []
    changed = False
    for item in all_items:
        item_id = str(item.get("id") or "").strip().lower()
        if item_id not in selected_ids:
            continue
        if not str(item.get("voiceId") or "").strip():
            continue
        item["owner"] = SUPER_ADMIN_USERNAME
        item["sourceCategory"] = "kesheng"
        item["provider"] = "aliyun"
        item["status"] = item.get("status") or "ready"
        item["label"] = item.get("label") or "已完成，可用于直播"
        item["promotedAt"] = now_iso()
        promoted.append({"id": item_id, "name": item.get("name", ""), "voiceId": item.get("voiceId", "")})
        changed = True

    if changed:
        save_voice_clone_jobs(all_items)
    return ok({"promoted": promoted, "count": len(promoted)}, f"已迁移 {len(promoted)} 个可升音色")


@app.delete("/api/voice-clone/jobs")
async def clear_voice_clone_jobs(token: str = ""):
    owner = require_username_from_token(token)
    all_items = load_voice_clone_jobs()
    owned_items = voice_clone_jobs_for_owner(owner)
    owned_ids = {str(item.get("id") or "") for item in owned_items}
    deleted_files = sum(1 for item in owned_items if delete_voice_clone_sample_file(item))
    save_voice_clone_jobs([item for item in all_items if str(item.get("id") or "") not in owned_ids])
    return ok({"cleared": True, "deleted": len(owned_items), "deletedFiles": deleted_files})


@app.delete("/api/voice-clone/jobs/{job_id}")
async def delete_voice_clone_job(job_id: str, token: str = ""):
    owner = require_username_from_token(token)
    if not re.fullmatch(r"[a-f0-9]{32}", job_id):
        raise HTTPException(status_code=400, detail="音色记录 ID 错误")
    all_items = load_voice_clone_jobs()
    target = next((item for item in all_items if str(item.get("id") or "") == job_id), None)
    if not target:
        raise HTTPException(status_code=404, detail="音色记录不存在")
    if is_super_admin_user(owner):
        if not is_shared_voice_clone_job(target):
            raise HTTPException(status_code=403, detail="超管只能在此删除可升音色")
    elif voice_clone_owner(target) != owner or is_shared_voice_clone_job(target):
        raise HTTPException(status_code=403, detail="只能删除当前账号自己的音色")
    deleted_file = delete_voice_clone_sample_file(target)
    save_voice_clone_jobs([item for item in all_items if str(item.get("id") or "") != job_id])
    return ok({"deleted": True, "id": job_id, "voiceId": target.get("voiceId", ""), "deletedFile": deleted_file})


@app.post("/api/send-verify-code")
async def send_verify_code(payload: SendVerifyCodeRequest):
    email = normalize_email(payload.email)
    users = load_users()
    if payload.codeType == "register" and user_by_email(users, email):
        raise HTTPException(status_code=409, detail="该邮箱已被注册")
    if payload.codeType == "reset_password" and not user_by_email(users, email):
        raise HTTPException(status_code=404, detail="该邮箱未注册")
    success, message = send_verify_email(email, payload.codeType)
    if not success:
        raise HTTPException(status_code=400, detail=message)
    return ok({"email": email, "codeType": payload.codeType}, "验证码已发送")


@app.post("/api/rewrite")
def rewrite_text(payload: RewriteRequest):
    text = normalize_text(payload.text)
    mode = payload.mode
    forbidden_words = normalize_forbidden_words(payload.forbiddenWords)
    try:
        ark_text = call_ark(text, payload.style, mode, forbidden_words)
        if ark_text:
            return ok({"text": apply_forbidden_words(ark_text, forbidden_words), "provider": "ark", "mode": mode})

        deepseek_text = call_deepseek(text, payload.style, mode, forbidden_words)
        if deepseek_text:
            return ok({"text": apply_forbidden_words(deepseek_text, forbidden_words), "provider": "deepseek", "mode": mode})

        return ok({"text": apply_forbidden_words(local_script(text, payload.style, mode), forbidden_words), "provider": current_model_provider(), "mode": mode})
    except Exception:
        return ok(
            {"text": apply_forbidden_words(local_script(text, payload.style, mode), forbidden_words), "provider": "local-fallback", "mode": mode},
            "模型暂不可用，已使用本地文案兜底",
        )


@app.post("/api/translate")
def translate_text(payload: TranslateRequest):
    text = normalize_text(payload.text)
    target_meta = TRANSLATION_TARGETS[payload.target]
    forbidden_words = normalize_forbidden_words(payload.forbiddenWords)
    if payload.target == "zh":
        try:
            translated, provider = call_translate(text, payload.style, payload.target, forbidden_words)
            if translated:
                return ok(translation_result(apply_forbidden_words(translated, forbidden_words), provider, payload.target, target_meta))
        except Exception:
            pass
        return ok(
            translation_result(apply_forbidden_words(local_script(text, payload.style, "rewrite"), forbidden_words), "local-fallback", payload.target, target_meta),
            "模型暂不可用，已使用本地中文优化兜底",
        )

    try:
        translated, provider = call_translate(text, payload.style, payload.target, forbidden_words)
        if translated:
            return ok(translation_result(apply_forbidden_words(translated, forbidden_words), provider, payload.target, target_meta))
    except Exception as exc:
        return ok(
            translation_result(apply_forbidden_words(local_translation_fallback(text, payload.target), forbidden_words), "local-fallback", payload.target, target_meta),
            f"翻译模型暂不可用，已保留原文，请稍后重试：{exc}",
        )

    return ok(
        translation_result(apply_forbidden_words(local_translation_fallback(text, payload.target), forbidden_words), "local-fallback", payload.target, target_meta),
        "未配置可用的大模型密钥，已保留原文；外语翻译需要配置 ARK_API_KEY/ARK_MODEL 或 DEEPSEEK_API_KEY",
    )


@app.post("/api/script/segments")
async def split_script(payload: ScriptSegmentRequest):
    segments = chunk_script(payload.text, payload.max_length)
    return ok([{"index": index + 1, "text": segment} for index, segment in enumerate(segments)])


@app.post("/api/live/line")
def live_line(payload: LiveLineRequest):
    text = normalize_text(payload.text)
    forbidden_words = normalize_forbidden_words(payload.forbiddenWords)
    if payload.mode == "off":
        return ok({"text": apply_forbidden_words(local_live_line(text, payload.mode, payload.round), forbidden_words), "provider": "original", "mode": payload.mode})

    try:
        ark_text = call_ark_live_line(text, payload.style, payload.mode, payload.round, forbidden_words)
        if ark_text:
            return ok({"text": apply_forbidden_words(ark_text, forbidden_words), "provider": "ark", "mode": payload.mode})

        deepseek_text = call_deepseek_live_line(text, payload.style, payload.mode, payload.round, forbidden_words)
        if deepseek_text:
            return ok({"text": apply_forbidden_words(deepseek_text, forbidden_words), "provider": "deepseek", "mode": payload.mode})

        return ok({"text": apply_forbidden_words(local_live_line(text, payload.mode, payload.round), forbidden_words), "provider": current_model_provider(), "mode": payload.mode})
    except Exception:
        return ok(
            {"text": apply_forbidden_words(local_live_line(text, payload.mode, payload.round), forbidden_words), "provider": "local-fallback", "mode": payload.mode},
            "模型暂不可用，已使用本地逐句文案兜底",
        )


@app.post("/api/douyin/start")
async def douyin_start(payload: CaptureStartRequest):
    _, state = douyin_capture_context(payload.token, payload.slotId, platform="douyin")
    return ok(start_douyin_fetcher(state, payload.url))


@app.post("/api/douyin/stop")
async def douyin_stop(payload: CaptureContextRequest):
    _, state = douyin_capture_context(payload.token, payload.slotId)
    return ok(stop_douyin_fetcher(state))


@app.get("/api/douyin/stop")
async def douyin_stop_get(token: str, slotId: str):
    _, state = douyin_capture_context(token, slotId)
    return ok(stop_douyin_fetcher(state))


@app.get("/api/douyin/status")
async def douyin_get_status(token: str, slotId: str):
    _, state = douyin_capture_context(token, slotId)
    return ok(douyin_status(state))


@app.post("/api/external-comments/start")
async def external_comments_start(payload: ExternalCaptureStartRequest):
    _, state = douyin_capture_context(payload.token, payload.slotId, platform=payload.platform)
    return ok(start_external_capture(state, payload.platform, payload.url))


@app.post("/api/external-comments/stop")
async def external_comments_stop(payload: ExternalCaptureStartRequest):
    _, state = douyin_capture_context(payload.token, payload.slotId, platform=payload.platform)
    return ok(stop_douyin_fetcher(state))


@app.post("/api/external-comments/ingest")
async def external_comments_ingest(payload: ExternalCommentIngestRequest):
    return ok(ingest_external_comment(payload))


@app.get("/api/comments")
async def get_comments(token: str, slotId: str, limit: int = 20):
    _, state = douyin_capture_context(token, slotId)
    safe_limit = max(1, min(limit, 100))
    items = list(state.get("comments") or [])[-safe_limit:]
    return ok({"items": items, "status": douyin_status(state)})


@app.post("/api/comments/reply")
def comment_reply(payload: CommentReplyRequest):
    comment = normalize_text(payload.comment)
    nickname = normalize_text(payload.nickname or "观众")
    script = normalize_text(payload.script)
    forbidden_words = normalize_forbidden_words(payload.forbiddenWords)
    prompt = build_comment_reply_prompt(comment, nickname, script, payload.style, forbidden_words)
    try:
        ark_text = call_ark_prompt(prompt, timeout=30)
        if ark_text:
            return ok({"text": apply_forbidden_words(ark_text, forbidden_words), "provider": "ark"})
        deepseek_text = call_deepseek_prompt(prompt, timeout=30)
        if deepseek_text:
            return ok({"text": apply_forbidden_words(deepseek_text, forbidden_words), "provider": "deepseek"})
        return ok({"text": apply_forbidden_words(local_comment_reply(comment, nickname, script), forbidden_words), "provider": current_model_provider()})
    except Exception:
        return ok({"text": apply_forbidden_words(local_comment_reply(comment, nickname, script), forbidden_words), "provider": "local-fallback"}, "模型暂不可用，已使用本地评论回复兜底")


@app.post("/api/time-announcement")
async def time_announcement(payload: TimeAnnouncementRequest):
    return ok({"text": beijing_time_text(payload.prefix), "timezone": "Asia/Shanghai"})


@app.post("/api/compute-recharge/orders")
async def create_compute_recharge_order(payload: ComputeRechargeCreateRequest):
    _, user = get_user_by_token(payload.token)
    raw_hours = float(payload.hours)
    amount = compute_recharge_amount(raw_hours)
    hours = int(raw_hours)
    if amount <= 0:
        raise HTTPException(status_code=400, detail="充值金额无效")

    order_id = f"KSCP{int(time.time())}{uuid.uuid4().hex[:8].upper()}"
    notify_url = get_wechat_notify_url()
    if not notify_url:
        raise HTTPException(status_code=500, detail="微信支付回调地址未配置")

    wechatpay = get_wechatpay_client()
    code, message = wechatpay.pay(
        description=f"可升Ai 算力充值 {hours:g}",
        out_trade_no=order_id,
        amount={"total": int(round(amount * 100))},
        attach=compact_payment_attach(
            "compute_recharge",
            user_id=user.get("id", ""),
            value=hours,
        ),
        notify_url=notify_url,
    )
    if code != 200:
        raise HTTPException(status_code=502, detail=f"创建微信支付订单失败：{message}")

    result = json.loads(message)
    code_url = result.get("code_url", "")
    if not code_url:
        raise HTTPException(status_code=502, detail="微信支付未返回二维码链接")

    order = {
        "orderId": order_id,
        "userId": user.get("id", ""),
        "username": user["username"],
        "hours": hours,
        "amount": amount,
        "status": "pending",
        "codeUrl": code_url,
        "createdAt": datetime.now(BEIJING_TZ).isoformat(),
    }
    COMPUTE_RECHARGE_ORDERS[order_id] = order
    save_compute_recharge_orders()
    return ok({**order, "qrDataUrl": compute_recharge_qr_data_url(code_url)})


@app.post("/api/compute-recharge/status")
async def compute_recharge_status(payload: ComputeRechargeStatusRequest):
    _, user = get_user_by_token(payload.token)
    order = COMPUTE_RECHARGE_ORDERS.get(payload.orderId)
    if not order:
        raise HTTPException(status_code=404, detail="订单不存在或服务已重启")
    if safe_normalize_username(str(order.get("username") or "")) != normalize_username(user["username"]):
        raise HTTPException(status_code=403, detail="无权查询该充值订单")
    if order.get("status") == "success":
        return ok(mark_compute_recharge_paid(payload.orderId))

    wechatpay = get_wechatpay_client()
    code, message = wechatpay.query(out_trade_no=payload.orderId)
    if code != 200:
        raise HTTPException(status_code=502, detail=f"查询微信支付订单失败：{message}")

    result = json.loads(message)
    trade_state = result.get("trade_state")
    if trade_state == "SUCCESS":
        return ok(mark_compute_recharge_paid(payload.orderId))
    if trade_state in {"PENDING", "NOTPAY", "USERPAYING"}:
        order["status"] = "pending"
        save_compute_recharge_orders()
        return ok(order)

    order["status"] = "failed"
    order["reason"] = result.get("trade_state_desc", "支付未成功")
    save_compute_recharge_orders()
    return ok(order)


@app.post("/api/live-slot-renewal/orders")
async def create_live_slot_renewal_order(payload: LiveSlotRenewalCreateRequest):
    users, user = get_user_by_token(payload.token)
    username = user["username"]
    profile = normalize_user_profile(user.get("profile"), username)
    slot = next((item for item in profile.get("liveSlots", []) if item.get("id") == payload.slotId), None)
    if not slot:
        raise HTTPException(status_code=404, detail="直播位不存在")

    plan = live_slot_renewal_plan(payload.plan)
    plan_days = int(plan["days"])
    plan_amount = float(plan["amount"])
    plan_name = str(plan["name"])
    order_id = f"KSLV{int(time.time())}{uuid.uuid4().hex[:8].upper()}"
    notify_url = get_wechat_notify_url()
    if not notify_url:
        raise HTTPException(status_code=500, detail="微信支付回调地址未配置")

    wechatpay = get_wechatpay_client()
    code, message = wechatpay.pay(
        description=f"可升Ai 直播位续费 {plan_name} {plan_days}天",
        out_trade_no=order_id,
        amount={"total": int(round(plan_amount * 100))},
        attach=compact_payment_attach(
            "live_slot_renewal",
            user_id=user.get("id", ""),
            slot_id=payload.slotId,
            value=plan_days,
        ),
        notify_url=notify_url,
    )
    if code != 200:
        raise HTTPException(status_code=502, detail=f"创建微信支付订单失败：{message}")

    result = json.loads(message)
    code_url = result.get("code_url", "")
    if not code_url:
        raise HTTPException(status_code=502, detail="微信支付未返回二维码链接")

    order = {
        "orderId": order_id,
        "type": "live_slot_renewal",
        "userId": user.get("id", ""),
        "username": username,
        "slotId": payload.slotId,
        "slotName": slot.get("name", "直播位"),
        "plan": payload.plan,
        "planName": plan_name,
        "days": plan_days,
        "amount": plan_amount,
        "status": "pending",
        "codeUrl": code_url,
        "createdAt": datetime.now(BEIJING_TZ).isoformat(),
    }
    COMPUTE_RECHARGE_ORDERS[order_id] = order
    save_compute_recharge_orders()
    logger.info(
        "live renewal order created order=%s userId=%s username=%s slotId=%s days=%s",
        order_id, user.get("id"), username, payload.slotId, plan_days,
    )
    return ok({**order, "qrDataUrl": compute_recharge_qr_data_url(code_url)})


@app.post("/api/live-slot-renewal/status")
async def live_slot_renewal_status(payload: ComputeRechargeStatusRequest):
    _, user = get_user_by_token(payload.token)
    order = COMPUTE_RECHARGE_ORDERS.get(payload.orderId)
    result = None
    if not order:
        wechatpay = get_wechatpay_client()
        code, message = wechatpay.query(out_trade_no=payload.orderId)
        if code != 200:
            raise HTTPException(status_code=404, detail=f"本地订单不存在，微信订单查询失败：{message}")
        result = json.loads(message)
        order = hydrate_payment_order(result)
        if not order:
            raise HTTPException(status_code=404, detail="微信订单未包含可恢复的直播位关联信息")
    if order.get("status") != "success" or not order.get("userId") or not order.get("slotId"):
        wechatpay = get_wechatpay_client()
        code, message = wechatpay.query(out_trade_no=payload.orderId)
        if code != 200:
            raise HTTPException(status_code=502, detail=f"查询微信支付订单失败：{message}")
        result = json.loads(message)
        order = hydrate_payment_order(result, order)
    if not order or order.get("type") != "live_slot_renewal":
        raise HTTPException(status_code=400, detail="该订单不是直播位续费订单")
    owner_matches = (
        str(order.get("userId") or "") == str(user.get("id") or "")
        or (
            not order.get("userId")
            and safe_normalize_username(str(order.get("username") or "")) == normalize_username(user["username"])
        )
    )
    if not owner_matches:
        raise HTTPException(status_code=403, detail="无权查询该直播位续费订单")
    if order.get("status") == "success":
        return ok(mark_live_slot_renewal_paid(payload.orderId))

    result = result or {}
    trade_state = result.get("trade_state")
    logger.info(
        "live renewal queried order=%s userId=%s slotId=%s tradeState=%s",
        payload.orderId, order.get("userId"), order.get("slotId"), trade_state,
    )
    if trade_state == "SUCCESS":
        return ok(mark_live_slot_renewal_paid(payload.orderId))
    if trade_state in {"PENDING", "NOTPAY", "USERPAYING"}:
        order["status"] = "pending"
        save_compute_recharge_orders()
        return ok(order)

    order["status"] = "failed"
    order["reason"] = result.get("trade_state_desc", "支付未成功")
    save_compute_recharge_orders()
    return ok(order)


@app.post("/api/live-slot-renewal/reconcile")
async def reconcile_live_slot_renewals(payload: AuthTokenRequest):
    users, user = get_user_by_token(payload.token)
    username = normalize_username(user["username"])
    user_id = str(user.get("id") or "")
    candidates = [
        order for order in COMPUTE_RECHARGE_ORDERS.values()
        if (order.get("type") == "live_slot_renewal" or str(order.get("orderId") or "").startswith("KSLV"))
        and not order.get("appliedAt")
    ]
    repaired = 0
    for order in sorted(candidates, key=lambda item: item.get("createdAt", ""), reverse=True)[:50]:
        try:
            if order.get("status") != "success" or not order.get("userId") or not order.get("slotId"):
                wechatpay = get_wechatpay_client()
                code, message = wechatpay.query(out_trade_no=order["orderId"])
                if code != 200:
                    continue
                result = json.loads(message)
                order = hydrate_payment_order(result, order) or order
                if result.get("trade_state") == "SUCCESS":
                    order["status"] = "success"
            owner_matches = (
                str(order.get("userId") or "") == user_id
                or (
                    not order.get("userId")
                    and safe_normalize_username(str(order.get("username") or "")) == username
                )
            )
            if not owner_matches:
                continue
            if order.get("paymentStatus") == "success" or order.get("status") in {"success", "paid_unapplied"}:
                applied = mark_live_slot_renewal_paid(order["orderId"])
                repaired += int(bool(applied and applied.get("appliedAt")))
        except Exception:
            continue
    users, user = get_user_by_token(payload.token)
    return ok({"repaired": repaired, "user": public_user(user)})


async def handle_compute_recharge_notify(request: Request):
    try:
        wechatpay = get_wechatpay_client()
        result = wechatpay.callback(headers=request.headers, body=await request.body())
        if not result:
            return {"code": "FAIL", "message": "签名验证失败"}
        hydrate_payment_order(result)
        logger.info(
            "payment notify order=%s type=%s userId=%s slotId=%s tradeState=%s",
            result.get("out_trade_no"),
            payment_attach(result).get("type"),
            payment_attach(result).get("userId"),
            payment_attach(result).get("slotId"),
            result.get("trade_state"),
        )
        if result.get("trade_state") == "SUCCESS":
            applied = mark_payment_order_paid(result.get("out_trade_no", ""))
            if applied and applied.get("type") == "live_slot_renewal" and not applied.get("appliedAt"):
                return {"code": "FAIL", "message": "付款已确认，直播位入账处理中"}
        return {"code": "SUCCESS", "message": "成功"}
    except Exception:
        return {"code": "FAIL", "message": "处理失败，请重试"}


@app.post("/api/compute-recharge/notify")
async def compute_recharge_notify(request: Request):
    return await handle_compute_recharge_notify(request)


@app.post("/api/payment/notify")
async def legacy_payment_notify(request: Request):
    return await handle_compute_recharge_notify(request)


@app.post("/api/tts")
async def tts(payload: TTSRequest):
    text = normalize_text(payload.text)
    provider, provider_voice = resolve_tts_voice(payload.voice, payload.token)
    extension = "wav" if provider == "aliyun" else "mp3"
    cache_key = hashlib.sha256(
        json.dumps(
            {
                "v": 1,
                "provider": provider,
                "voice": provider_voice,
                "rate": payload.rate,
                "pitch": payload.pitch,
                "text": text,
            },
            ensure_ascii=False,
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()
    file_id = f"{cache_key[:32]}.{extension}"
    output_path = AUDIO_DIR / file_id

    try:
        AUDIO_DIR.mkdir(exist_ok=True)
        if output_path.exists() and output_path.stat().st_size > 0:
            logger.info("tts cache hit provider=%s voice=%s chars=%s file=%s", provider, provider_voice, len(text), file_id)
            return ok({"url": f"/audio/{file_id}", "fileName": file_id, "textLength": len(text), "provider": provider, "cached": True})

        with TTS_CACHE_LOCKS_GUARD:
            cache_lock = TTS_CACHE_LOCKS.setdefault(cache_key, asyncio.Lock())

        started_at = time.perf_counter()
        async with cache_lock:
            if output_path.exists() and output_path.stat().st_size > 0:
                elapsed_ms = int((time.perf_counter() - started_at) * 1000)
                logger.info("tts cache hit after wait provider=%s voice=%s chars=%s elapsedMs=%s file=%s", provider, provider_voice, len(text), elapsed_ms, file_id)
                return ok({"url": f"/audio/{file_id}", "fileName": file_id, "textLength": len(text), "provider": provider, "cached": True, "elapsedMs": elapsed_ms})

            if provider == "aliyun":
                await asyncio.to_thread(synthesize_aliyun_tts, text, provider_voice, payload.rate, payload.pitch, output_path)
            else:
                await synthesize_edge_tts(text, provider_voice, payload.rate, payload.pitch, output_path)

        elapsed_ms = int((time.perf_counter() - started_at) * 1000)
        logger.info("tts synthesized provider=%s voice=%s chars=%s elapsedMs=%s file=%s", provider, provider_voice, len(text), elapsed_ms, file_id)
        return ok({"url": f"/audio/{file_id}", "fileName": file_id, "textLength": len(text), "provider": provider, "cached": False, "elapsedMs": elapsed_ms})
    except Exception as exc:
        logger.exception("tts failed provider=%s voice=%s chars=%s file=%s", provider, provider_voice, len(text), file_id)
        raise HTTPException(status_code=500, detail=f"语音合成失败：{exc}")


@app.get("/audio/{file_name}")
async def get_audio(file_name: str):
    if not re.fullmatch(r"[a-f0-9]{32}\.(mp3|wav|ogg|webm|flac|aac|m4a)", file_name):
        raise HTTPException(status_code=400, detail="文件名错误")

    media_types = {
        ".mp3": "audio/mpeg",
        ".wav": "audio/wav",
        ".ogg": "audio/ogg",
        ".webm": "audio/webm",
        ".flac": "audio/flac",
        ".aac": "audio/aac",
        ".m4a": "audio/mp4",
    }
    path = AUDIO_DIR / file_name
    if not path.exists():
        raise HTTPException(status_code=404, detail="文件不存在")
    return FileResponse(
        path,
        media_type=media_types.get(path.suffix.lower(), "audio/mpeg"),
        filename=file_name,
        headers={"Cache-Control": "public, max-age=31536000, immutable"},
    )


@app.get("/data/assets/{file_name}")
@app.get("/api/assets/{file_name}")
async def get_data_asset(file_name: str):
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", file_name):
        raise HTTPException(status_code=400, detail="文件名错误")
    path = DATA_ASSETS_DIR / file_name
    if (not path.exists() or not path.is_file()) and file_name in {"gzh.jpg", "jiaocheng.mp4"}:
        path = GUIDE_MEDIA_DIR / file_name
    if not path.exists() or not path.is_file():
        raise HTTPException(status_code=404, detail="文件不存在")
    media_types = {
        ".png": "image/png",
        ".ico": "image/x-icon",
        ".jpg": "image/jpeg",
        ".jpeg": "image/jpeg",
        ".webp": "image/webp",
        ".gif": "image/gif",
        ".svg": "image/svg+xml",
        ".mp4": "video/mp4",
    }
    return FileResponse(path, media_type=media_types.get(path.suffix.lower(), "application/octet-stream"))


@app.get("/api/guide-media/{file_name}")
async def get_guide_media(file_name: str):
    allowed_files = {
        "jiaocheng.mp4": "video/mp4",
        "gzh.jpg": "image/jpeg",
    }
    media_type = allowed_files.get(file_name)
    if not media_type:
        raise HTTPException(status_code=400, detail="文件名错误")
    path = GUIDE_MEDIA_DIR / file_name
    if not path.exists() or not path.is_file():
        raise HTTPException(status_code=404, detail="文件不存在")
    return FileResponse(path, media_type=media_type)


def build_comment_plugin_zip(platform: str) -> bytes:
    plugin_dir = COMMENT_PLUGIN_DIRS.get(platform)
    if not plugin_dir or not plugin_dir.exists() or not plugin_dir.is_dir():
        raise HTTPException(status_code=404, detail=f"{PLATFORM_LABELS.get(platform, platform)}评论采集插件不存在")
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path in plugin_dir.rglob("*"):
            if not path.is_file():
                continue
            archive.write(path, path.relative_to(plugin_dir).as_posix())
    buffer.seek(0)
    return buffer.getvalue()


@app.get("/api/downloads/{platform}-comment-plugin.zip")
async def download_platform_comment_plugin(platform: str):
    if platform not in COMMENT_PLUGIN_DIRS:
        raise HTTPException(status_code=404, detail="评论采集插件不存在")
    return Response(
        content=build_comment_plugin_zip(platform),
        media_type="application/zip",
        headers={"Content-Disposition": f'attachment; filename="{platform}-comment-plugin.zip"'},
    )


@app.get("/api/downloads/kuaishou-comment-plugin.zip")
async def download_kuaishou_comment_plugin():
    return await download_platform_comment_plugin("kuaishou")


@app.get("/ksksks")
async def admin_index():
    if not ADMIN_FILE.exists():
        raise HTTPException(status_code=404, detail="后台页面不存在")
    return FileResponse(
        ADMIN_FILE,
        headers={
            "Cache-Control": "no-store, no-cache, must-revalidate, max-age=0",
            "Pragma": "no-cache",
            "Expires": "0",
        },
    )


@app.get("/")
async def index():
    if not INDEX_FILE.exists():
        raise HTTPException(status_code=404, detail="首页文件不存在")
    return FileResponse(
        INDEX_FILE,
        headers={
            "Cache-Control": "no-store, no-cache, must-revalidate, max-age=0",
            "Pragma": "no-cache",
            "Expires": "0",
        },
    )


if __name__ == "__main__":
    import uvicorn

    uvicorn.run(app, host="0.0.0.0", port=5550)
