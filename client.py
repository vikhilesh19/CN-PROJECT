
import socket
import threading
import json
import os
import re
import uuid
import time
import base64
import io
import tkinter as tk
from tkinter import ttk, messagebox, colorchooser, simpledialog, filedialog
from datetime import datetime
from collections import deque
import socket as socket_module

FREE = {"pen", "freehand", "marker", "highlighter", "eraser"}
SHAPES = {"line", "rectangle", "oval", "circle", "triangle"}

TOOLS = [
    "pen", "freehand", "line", "rectangle", "circle",
    "oval", "triangle", "marker", "highlighter",
    "text", "eraser", "laser", "sticky note", "select"
]

BG = "#F1F5F9"
WHITE = "#FFFFFF"
NAVY = "#17243B"
PANEL = "#22324D"
BLUE = "#4F46E5"
GREEN = "#059669"
RED = "#E11D48"
PURPLE = "#7C3AED"
TEXT = "#17243B"
MUTED = "#64748B"


# ---------- ROUNDED COMPONENTS ----------

def rounded_rectangle(canvas, x1, y1, x2, y2, radius,
                      fill, outline="", width=1):

    r = min(radius, (x2-x1)/2, (y2-y1)/2)

    points = [
        x1+r, y1, x1+r, y1,
        x2-r, y1, x2-r, y1,
        x2, y1, x2, y1+r,
        x2, y2-r, x2, y2-r,
        x2, y2, x2-r, y2,
        x1+r, y2, x1+r, y2,
        x1, y2, x1, y2-r,
        x1, y1+r, x1, y1+r,
        x1, y1
    ]

    return canvas.create_polygon(
        points,
        smooth=True,
        splinesteps=24,
        fill=fill,
        outline=outline,
        width=width
    )


class RoundedEntry(tk.Frame):
    def __init__(self, parent, variable, show="",
                 width=320, height=48):

        super().__init__(parent, bg=WHITE)

        self.canvas = tk.Canvas(
            self, width=width, height=height,
            bg=WHITE, highlightthickness=0
        )
        self.canvas.pack()

        self.border = rounded_rectangle(
            self.canvas, 2, 2, width-2, height-2,
            12, WHITE, "#CBD5E1", 2
        )

        self.entry = tk.Entry(
            self.canvas,
            textvariable=variable,
            show=show,
            bg=WHITE,
            fg=TEXT,
            insertbackground=BLUE,
            font=("Segoe UI", 11),
            relief="flat",
            borderwidth=0,
            highlightthickness=0
        )

        self.canvas.create_window(
            (width-18)/2, height/2,
            window=self.entry,
            width=width-(70 if show else 32),
            height=height-16
        )

        if show:
            self.password_visible = False
            self.eye_button = tk.Button(
                self.canvas, text="👁", font=("Segoe UI", 13),
                bg=WHITE, fg=TEXT, relief="flat", bd=0,
                cursor="hand2", takefocus=0,
                command=self.toggle_password
            )
            self.canvas.create_window(
                width-25, height/2, window=self.eye_button,
                width=32, height=32
            )

        self.entry.bind(
            "<FocusIn>",
            lambda e: self.canvas.itemconfigure(
                self.border, outline=BLUE
            )
        )

        self.entry.bind(
            "<FocusOut>",
            lambda e: self.canvas.itemconfigure(
                self.border, outline="#CBD5E1"
            )
        )

        self.canvas.bind(
            "<Button-1>",
            lambda e: self.entry.focus_set()
        )


    def toggle_password(self):
        self.password_visible = not self.password_visible
        self.entry.configure(show="" if self.password_visible else "*")
        self.eye_button.configure(text="🙈" if self.password_visible else "👁")


class RoundedButton(tk.Canvas):
    def __init__(self, parent, text, command,
                 bg_color=BLUE, hover="#4338CA",
                 width=320, height=48):

        super().__init__(
            parent, width=width, height=height,
            bg=WHITE, highlightthickness=0,
            cursor="hand2"
        )

        self.normal = bg_color
        self.hover = hover
        self.command = command

        self.shape = rounded_rectangle(
            self, 2, 2, width-2, height-2,
            12, bg_color
        )

        self.create_text(
            width/2, height/2,
            text=text,
            fill=WHITE,
            font=("Segoe UI", 11, "bold")
        )

        self.bind(
            "<Enter>",
            lambda e: self.itemconfigure(
                self.shape, fill=self.hover
            )
        )

        self.bind(
            "<Leave>",
            lambda e: self.itemconfigure(
                self.shape, fill=self.normal
            )
        )

        self.bind(
            "<Button-1>",
            lambda e: self.command()
        )


# ---------- MAIN APPLICATION ----------

class Whiteboard:

    def __init__(self):

        self.root = tk.Tk()
        self.root.title("White Board | Collaborative Whiteboard")
        self.root.geometry("1250x780")
        self.root.minsize(980, 620)
        self.root.configure(bg=BG)

        self.dark_mode = False
        self.sock = None
        self.send_lock = threading.Lock()

        self.username = ""
        self.role = ""
        self.password = ""
        self.server_ip = "127.0.0.1"
        self.server_port = 5000
        self.last_ping = None
        self.ping_sent = {}
        self.recent_colors = [BLUE, "#E11D48", "#059669", "#F59E0B", "#111827"]
        self.tool_buttons = {}
        self.unread = 0
        self.chat_collapsed = False
        self.chat_locked = False
        self.chat_muted = []
        self.chat_slow = 0
        self.chat_settings_button = None
        self.toast_widget = None
        self.toast_timer = None
        try:
            with open(os.path.join(os.path.expanduser("~"), ".whiteboard_connection.json"), encoding="utf-8") as f:
                config = json.load(f)
            self.server_ip = str(config.get("ip", self.server_ip))
            self.server_port = int(config.get("port", 5000))
        except (OSError, ValueError, TypeError):
            pass
        self.room = ""
        self.room_password = ""

        self.owner = False
        self.meeting_owner = ""
        self.locked = False
        self.connected = False
        self.reconnecting = False
        self.reconnect_busy = False
        self.recovery_sync_ready = False
        self.recovery_resync_needed = False
        self.closing = False
        self.page = "login"

        self.strokes = []
        self.chat_history = []
        self.pending = []
        self.participants = []
        self.raised_hands = set()
        self.hand_button = None

        self.color = BLUE
        self.tool = "pen"
        self.start_point = None
        self.last = None
        self.active_stroke_group = None
        self.preview = None
        self.grid_visible = False
        self.selected_object = None
        self.object_drag = None
        self.image_refs = {}

        self.remote_cursors = {}
        self.remote_previews = {}
        self.remote_text_previews = {}
        self.last_text_preview_send = 0
        self.cursor_items = {}
        self.below_indicators = {}
        self.local_laser = None

        self.last_cursor_send = 0
        self.last_preview_send = 0

        self.board_width = 3000
        self.board_height = 3000
        self.expand_amount = 1500
        self.max_height = 1000000

        # Participant notifications
        self.participants_loaded = False
        self.notification_queue = deque()
        self.notification_active = False
        self.notification = None
        self.notification_after = None

        self.setup_theme()
        # Bind exact key sequences at the application level.  The handler is
        # installed after each board build as well, so recreated widgets work.
        self.install_keyboard_shortcuts()
        self.build_login()

        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.mainloop()

    # ---------- THEME ----------

    def setup_theme(self):

        style = ttk.Style()
        style.theme_use("clam")

        style.configure(
            "TFrame", background=BG
        )

        style.configure(
            "TLabel",
            background=BG,
            foreground=TEXT,
            font=("Segoe UI", 10)
        )

        style.configure(
            "TEntry",
            padding=9,
            fieldbackground=WHITE
        )

        style.configure(
            "TCombobox",
            padding=7,
            fieldbackground=WHITE
        )

        style.configure(
            "TSpinbox",
            padding=5,
            fieldbackground=WHITE
        )

        styles = {
            "Primary": (BLUE, "#4338CA", WHITE),
            "Success": (GREEN, "#047857", WHITE),
            "Danger": (RED, "#BE123C", WHITE),
            "Purple": (PURPLE, "#6D28D9", WHITE),
            "Soft": ("#E0E7FF", "#C7D2FE", BLUE),
            "Dark": (PANEL, "#334765", WHITE)
        }

        for name, (normal, active, foreground) in styles.items():

            style.configure(
                name + ".TButton",
                background=normal,
                foreground=foreground,
                padding=(12, 9),
                font=("Segoe UI", 10, "bold"),
                borderwidth=0,
                relief="flat"
            )

            style.map(
                name + ".TButton",
                background=[
                    ("disabled", "#CBD5E1"),
                    ("active", active)
                ],
                foreground=[
                    ("disabled", MUTED),
                    ("active", foreground)
                ]
            )

        style.configure(
            "Dark.TFrame",
            background=NAVY
        )

        style.configure(
            "DarkTitle.TLabel",
            background=NAVY,
            foreground=WHITE,
            font=("Segoe UI", 13, "bold")
        )

        style.configure(
            "Toolbar.TFrame",
            background=WHITE
        )

        style.configure(
            "Toolbar.TLabel",
            background=WHITE,
            foreground=TEXT,
            font=("Segoe UI", 10, "bold")
        )

    def clear_page(self):

        self.reset_notifications()

        for widget in self.root.winfo_children():
            widget.destroy()

    def card(self, parent, width=420, height=600):

        canvas = tk.Canvas(
            parent,
            width=width,
            height=height,
            bg=BG,
            highlightthickness=0
        )
        canvas.pack()

        rounded_rectangle(
            canvas, 3, 3,
            width-3, height-3,
            22, WHITE, "#E2E8F0"
        )

        frame = tk.Frame(canvas, bg=WHITE)

        canvas.create_window(
            width/2, height/2,
            window=frame,
            width=width-70,
            height=height-45
        )

        return frame

    def rounded_field(self, parent, label, variable, secret=False):

        tk.Label(
            parent,
            text=label,
            bg=WHITE,
            fg=TEXT,
            font=("Segoe UI", 10, "bold")
        ).pack(anchor="w", pady=(12, 6))

        box = RoundedEntry(
            parent,
            variable,
            show="*" if secret else ""
        )
        box.pack()

        return box.entry

    # ---------- LOGIN ----------

    def build_login(self):

        self.page = "login"
        self.clear_page()

        outer = tk.Frame(self.root, bg=BG)
        outer.pack(expand=True)

        card = self.card(outer, 420, 650)

        tk.Label(
            card,
            text="White Board",
            font=("Segoe UI", 27, "bold"),
            fg=NAVY,
            bg=WHITE
        ).pack(pady=(10, 4))

        tk.Label(
            card,
            text="Create  •  Collaborate  •  Connect",
            font=("Segoe UI", 10),
            fg=MUTED,
            bg=WHITE
        ).pack(pady=(0, 20))

        self.ip_var = tk.StringVar(value=self.server_ip)
        self.port_var = tk.StringVar(value=str(self.server_port))
        self.rounded_field(card, "Server Port", self.port_var)
        self.name_var = tk.StringVar(value=self.username)
        self.pass_var = tk.StringVar()
        self.role_var = tk.StringVar(value="student")

        self.rounded_field(
            card, "Server IP Address", self.ip_var
        )

        tk.Label(
            card,
            text="Login as",
            bg=WHITE,
            fg=TEXT,
            font=("Segoe UI", 10, "bold")
        ).pack(anchor="w", pady=(16, 7))

        roles = tk.Frame(card, bg=WHITE)
        roles.pack(anchor="w")

        for role in ("host", "student"):

            tk.Radiobutton(
                roles,
                text=role.title(),
                variable=self.role_var,
                value=role,
                bg=WHITE,
                fg=TEXT,
                selectcolor=WHITE,
                activebackground=WHITE,
                font=("Segoe UI", 10)
            ).pack(side="left", padx=(0, 28))

        self.rounded_field(
            card, "Username", self.name_var
        )

        password_entry = self.rounded_field(
            card, "Password", self.pass_var, True
        )

        password_entry.bind("<Return>", lambda e: self.login())
        self.root.bind("<Return>", lambda e: self.login() if self.page == "login" else None)

        tk.Frame(
            card, bg=WHITE, height=22
        ).pack()

        RoundedButton(
            card,
            "Login to Whiteboard",
            self.login
        ).pack()

        tk.Label(
            card,
            text="Private LAN collaboration",
            bg=WHITE,
            fg=MUTED,
            font=("Segoe UI", 9)
        ).pack(pady=(18, 0))

    # ---------- CONNECTION ----------

    def connect(self):

        try:
            sock = socket.create_connection(
                (self.server_ip, self.server_port),
                timeout=3
            )

            sock.settimeout(None)
            self.sock = sock

            threading.Thread(
                target=self.receive,
                args=(sock,),
                daemon=True
            ).start()

            return True

        except OSError:
            return False

    def login(self):

        if not self.name_var.get().strip() or not self.pass_var.get():

            messagebox.showerror(
                "Error",
                "Enter username and password"
            )
            return

        self.username = self.name_var.get().strip()
        self.password = self.pass_var.get()
        self.role = self.role_var.get()
        self.server_ip = self.ip_var.get().strip()
        try:
            self.server_port = int(self.port_var.get())
            if not 1 <= self.server_port <= 65535:
                raise ValueError
        except ValueError:
            self.toast("Port must be between 1 and 65535", "error")
            return
        try:
            with open(os.path.join(os.path.expanduser("~"), ".whiteboard_connection.json"), "w", encoding="utf-8") as f:
                json.dump({"ip": self.server_ip, "port": self.server_port}, f)
        except OSError:
            pass

        if not self.connect():

            messagebox.showerror(
                "Error",
                "Cannot connect to server"
            )
            return

        self.send({
            "type": "login",
            "username": self.username,
            "password": self.password,
            "role": self.role
        })

    # ---------- DASHBOARD ----------

    def build_dashboard(self):

        self.page = "dashboard"
        self.clear_page()

        outer = tk.Frame(self.root, bg=BG)
        outer.pack(expand=True)

        card = self.card(outer, 440, 400)

        tk.Label(
            card,
            text="Welcome back!",
            font=("Segoe UI", 24, "bold"),
            fg=NAVY,
            bg=WHITE
        ).pack(pady=(20, 8))

        tk.Label(
            card,
            text=self.username + "  •  " + self.role.title(),
            font=("Segoe UI", 11),
            fg=MUTED,
            bg=WHITE
        ).pack(pady=(0, 25))

        if self.role == "host":

            RoundedButton(
                card,
                "Create New Meeting",
                lambda: self.room_form("create")
            ).pack(pady=7)

        RoundedButton(
            card,
            "Join Existing Meeting",
            lambda: self.room_form("join"),
            GREEN, "#047857"
        ).pack(pady=7)

        if self.role == "host":

            RoundedButton(
                card,
                "Add Host / Student",
                self.add_user_form,
                PURPLE, "#6D28D9"
            ).pack(pady=7)

    # ---------- CREATE / JOIN ----------

    def room_form(self, mode):

        self.page = "room_form"
        self.clear_page()

        outer = tk.Frame(self.root, bg=BG)
        outer.pack(expand=True)

        card = self.card(outer, 420, 520)

        tk.Label(
            card,
            text=mode.title() + " Meeting",
            font=("Segoe UI", 22, "bold"),
            fg=NAVY,
            bg=WHITE
        ).pack(pady=(12, 16))

        room = tk.StringVar()
        password = tk.StringVar()

        self.rounded_field(
            card, "Room ID", room
        )

        if mode == "create":
            def generate_room_id():
                self.room_id_field = room
                self.send({"type": "generate_room_id"})

            RoundedButton(
                card, "Generate Random Room ID",
                generate_room_id, GREEN, "#047857"
            ).pack(pady=(6, 0))

        self.rounded_field(
            card, "Room Password", password, True
        )

        def submit():

            if not room.get().strip() or not password.get():

                messagebox.showerror(
                    "Error",
                    "Enter room details"
                )
                return

            self.room = room.get().strip().upper()
            self.room_password = password.get()

            self.send({
                "type": mode,
                "room": self.room,
                "password": self.room_password
            })

        tk.Frame(
            card, bg=WHITE, height=12
        ).pack()

        RoundedButton(
            card,
            "Create Meeting" if mode == "create"
            else "Join Meeting",
            submit
        ).pack(pady=(8, 10))

        RoundedButton(
            card,
            "Back to Dashboard",
            self.build_dashboard,
            GREEN, "#047857"
        ).pack(pady=(0, 8))

    # ---------- ADD USER ----------

    def add_user_form(self):

        if self.role != "host":
            return

        window = tk.Toplevel(self.root)
        window.title("Add New User")
        window.geometry("420x480")
        window.configure(bg=BG)

        outer = tk.Frame(window, bg=BG)
        outer.pack(expand=True)

        canvas = tk.Canvas(
            outer,
            width=390,
            height=450,
            bg=BG,
            highlightthickness=0
        )
        canvas.pack()

        rounded_rectangle(
            canvas, 3, 3, 387, 447,
            20, WHITE, "#E2E8F0"
        )

        frame = tk.Frame(canvas, bg=WHITE)

        canvas.create_window(
            195, 225,
            window=frame,
            width=330,
            height=420
        )

        name = tk.StringVar()
        password = tk.StringVar()
        role = tk.StringVar(value="student")

        tk.Label(
            frame,
            text="Create Account",
            font=("Segoe UI", 18, "bold"),
            bg=WHITE,
            fg=NAVY
        ).pack(pady=(5, 12))

        self.rounded_field(
            frame, "Username", name
        )

        self.rounded_field(
            frame, "Password", password, True
        )

        for item in ("host", "student"):

            tk.Radiobutton(
                frame,
                text=item.title(),
                variable=role,
                value=item,
                bg=WHITE,
                selectcolor=WHITE
            ).pack(anchor="w")

        def add():

            if not name.get().strip() or not password.get():

                messagebox.showerror(
                    "Error",
                    "Enter all details"
                )
                return

            self.send({
                "type": "add_user",
                "username": name.get().strip(),
                "password": password.get(),
                "role": role.get()
            })

            window.destroy()

        RoundedButton(
            frame,
            "Create Account",
            add
        ).pack(pady=12)

    # ---------- PARTICIPANT NOTIFICATIONS ----------

    def reset_notifications(self):

        if self.notification_after is not None:

            try:
                self.root.after_cancel(
                    self.notification_after
                )
            except (tk.TclError, ValueError):
                pass

        self.notification_after = None
        self.notification_queue.clear()
        self.notification_active = False

        if self.notification is not None:

            try:
                self.notification.destroy()
            except tk.TclError:
                pass

        self.notification = None

    def show_notification(self, username, action):

        if self.page != "board":
            return

        if username == self.username and action not in ("raised hand",):
            return

        self.notification_queue.append(
            (username, action)
        )

        if not self.notification_active:
            self.display_next_notification()

    def display_next_notification(self):

        if self.page != "board":
            self.reset_notifications()
            return

        if not self.notification_queue:
            self.notification_active = False
            return

        self.notification_active = True

        username, action = self.notification_queue.popleft()

        joined = action == "joined"
        hand = action == "raised hand"

        accent = "#34D399" if joined else "#FBBF24"
        icon = "!" if hand else ("+" if joined else "-")

        message = (
            f"{username} raised a hand" if hand else (
                f"{username} joined the meeting" if joined
                else f"{username} left the meeting")
        )

        subtitle = (
            "Hand raised" if hand else (
                "A participant has connected" if joined
                else "A participant has disconnected")
        )

        # Floating card
        self.notification = tk.Frame(
            self.root,
            bg=NAVY,
            highlightbackground=accent,
            highlightthickness=2
        )

        inner = tk.Frame(
            self.notification,
            bg=NAVY
        )
        inner.pack(padx=16, pady=11)

        icon_box = tk.Label(
            inner,
            text=icon,
            bg="#263851",
            fg=accent,
            font=("Segoe UI", 20, "bold"),
            width=3,
            height=2
        )
        icon_box.pack(side="left", padx=(0, 12))

        details = tk.Frame(
            inner, bg=NAVY
        )
        details.pack(side="left")

        tk.Label(
            details,
            text=message,
            bg=NAVY,
            fg=WHITE,
            font=("Segoe UI", 12, "bold")
        ).pack(anchor="w")

        tk.Label(
            details,
            text=subtitle,
            bg=NAVY,
            fg="#CBD5E1",
            font=("Segoe UI", 9)
        ).pack(anchor="w", pady=(4, 0))

        self.notification.place(
            relx=0.5,
            rely=1.0,
            y=-85,
            anchor="s"
        )

        self.notification.lift()

        # Automatically hide after one second
        self.notification_after = self.root.after(
            1000,
            self.hide_notification
        )

    def hide_notification(self):

        self.notification_after = None

        if self.notification is not None:

            try:
                self.notification.destroy()
            except tk.TclError:
                pass

        self.notification = None
        self.notification_active = False

        if self.notification_queue:
            self.display_next_notification()

    def update_participants(self, msg):

        new_users = [
            user["name"]
            for user in msg.get("users", [])
        ]

        old_users = self.participants.copy()

        if self.participants_loaded:

            for name in new_users:

                if name not in old_users:
                    self.show_notification(name, "joined")
                    self.add_system_line(f"{name} joined")

            for name in old_users:

                if name not in new_users:
                    self.show_notification(name, "left")
                    self.add_system_line(f"{name} left")

        self.participants_loaded = True

        self.users.delete(0, "end")
        self.participants = []

        self.participant_colors = {u["name"]: u.get("color", WHITE) for u in msg.get("users", [])}
        for user in msg.get("users", []):

            name = user["name"]
            self.participants.append(name)
            if user.get("hand_raised"):
                self.raised_hands.add(name)
            else:
                self.raised_hands.discard(name)

            label = (
                f"{name} ({user['role'].title()})"
            )

            if name == msg.get("owner"):
                label += " - Owner"
            if name in self.raised_hands:
                label += "  [HAND RAISED]"

            label = ("● " + name + (" (you)" if name == self.username else "") +
                     (" [HOST]" if user.get("role") == "host" else "") +
                     (" [OWNER]" if name == msg.get("owner") else "") +
                     (" ✋" if name in self.raised_hands else ""))
            self.users.insert("end", label)
            try:
                self.users.itemconfig("end", fg=user.get("color", WHITE))
            except tk.TclError:
                pass

        self.meeting_owner = msg.get(
            "owner", ""
        )

        self.owner = (
            self.meeting_owner == self.username
        )

        for name in list(self.remote_cursors):

            if name not in self.participants:
                self.remove_remote_cursor(name)

        for name in list(self.remote_previews):

            if name not in self.participants:
                self.clear_shape_preview(name)
        for name in list(self.remote_text_previews):
            if name not in self.participants:
                self.clear_text_preview(name)

        self.update_hand_button()
        self.update_buttons()

    # ---------- WHITEBOARD GUI ----------

    def toggle_dark_mode(self):
        if self.page != "board":
            return
        self.dark_mode = not self.dark_mode
        self.apply_board_theme()

    def apply_board_theme(self):
        if self.page != "board":
            return
        dark = self.dark_mode
        # Only theme the interface: drawing strokes, user-selected colors,
        # selection handles and tool state are never modified.
        palette = {
            "#F1F5F9": "#0F172A",
            "#FFFFFF": "#172033",
            "#E2E8F0": "#263449",
            "#E5E7EB": "#334155",
            "#E0E7FF": "#303C64",
            "#17243B": "#101A2E",
            "#22324D": "#1A2940",
            "#334155": "#25364E",
            "#CBD5E1": "#516178",
            "#475569": "#C4D2E6",
            "#64748B": "#A7B7CC",
            "#111827": "#E6EDF8",
            "#C7D2FE": "#C7D2FE",
        }
        reverse = {v.upper(): k for k, v in palette.items()}
        forward = {k.upper(): v for k, v in palette.items()}
        colors = forward if dark else reverse

        def convert(value):
            return colors.get(str(value).upper(), value)

        def recolor(widget):
            try:
                cls = widget.winfo_class()
                if cls in ("Frame", "LabelFrame", "Canvas", "Label", "Button", "Entry", "Text", "Listbox"):
                    opts = widget.configure()
                    updates = {}
                    for key in ("bg", "fg", "activebackground", "activeforeground",
                                "insertbackground", "selectbackground", "highlightbackground"):
                        if key in opts:
                            old = widget.cget(key)
                            new = convert(old)
                            if key in ("fg", "activeforeground", "insertbackground"):
                                # White text on dark controls must remain white.
                                if str(old).upper() in ("#FFFFFF", "WHITE"):
                                    new = "#FFFFFF"
                                elif dark and str(old).upper() in ("#17243B", "#111827"):
                                    new = "#E6EDF8"
                                elif not dark and str(old).upper() == "#E6EDF8":
                                    new = "#17243B"
                            if new != old:
                                updates[key] = new
                    if updates:
                        widget.configure(**updates)
            except (tk.TclError, ValueError):
                pass
            for child in widget.winfo_children():
                recolor(child)

        recolor(self.root)
        # Keep the title and room information readable on the navy header.
        if hasattr(self, "board_header") and self.board_header.winfo_exists():
            for child in self.board_header.winfo_children():
                if isinstance(child, tk.Label) and child is not self.connection_pill:
                    label_text = str(child.cget("text"))
                    child.configure(fg="#FFFFFF" if label_text == "White Board" else "#C7D2FE")
        self.root.configure(bg="#0F172A" if dark else BG)
        self.canvas.configure(bg="#101827" if dark else WHITE)
        self.theme_button.configure(text="☀" if dark else "☾")
        style = ttk.Style()
        style.configure("TFrame", background="#0F172A" if dark else BG)
        style.configure("TLabel", background="#0F172A" if dark else BG,
                        foreground="#E6EDF8" if dark else TEXT)
        style.configure("Toolbar.TFrame", background="#172033" if dark else WHITE)
        style.configure("Toolbar.TLabel", background="#172033" if dark else WHITE,
                        foreground="#E6EDF8" if dark else TEXT)
        style.configure("TEntry", fieldbackground="#263449" if dark else WHITE,
                        foreground="#E6EDF8" if dark else TEXT)
        style.configure("TSpinbox", fieldbackground="#263449" if dark else WHITE,
                        foreground="#E6EDF8" if dark else TEXT)
        style.configure("TCombobox", fieldbackground="#263449" if dark else WHITE,
                        foreground="#E6EDF8" if dark else TEXT)
        style.configure("Soft.TButton", background="#303C64" if dark else "#E0E7FF",
                        foreground="#E6EDF8" if dark else BLUE)
        # Preserve all shared whiteboard strokes; only recolor local grid lines.
        if self.grid_visible:
            self.canvas.itemconfigure("grid", fill="#334155" if dark else "#E9EDF4")
        self.update_color_button()
        self.refresh_tool_rail()
        self.update_hand_button()

    def build_board(self):

        self.page = "board"
        self.clear_page()
        self.tool_buttons = {}

        self.participants_loaded = False
        self.participants = []
        self.participant_colors = {}
        self.raised_hands = set()
        self.hand_button = None
        self.unread = 0
        self.chat_collapsed = False

        self.remote_cursors = {}
        self.remote_previews = {}
        self.remote_text_previews = {}
        self.last_text_preview_send = 0
        self.cursor_items = {}
        self.below_indicators = {}
        self.local_laser = None
        self.selected_text = None
        self.selected_object = None
        self.object_drag = None
        self.image_refs = {}
        self.text_drag = None
        self.text_selection_box = None
        self.text_drag_mode = None

        header = tk.Frame(
            self.root,
            bg=NAVY,
            height=55
        )
        header.pack(fill="x")
        self.board_header = header
        header.pack_propagate(False)

        tk.Label(
            header,
            text="White Board",
            bg=NAVY,
            fg=WHITE,
            font=("Segoe UI", 17, "bold")
        ).pack(side="left", padx=20)

        tk.Label(
            header,
            text="Room ID: " + self.room,
            bg=NAVY,
            fg="#C7D2FE",
            font=("Segoe UI", 11, "bold")
        ).pack(side="left", padx=(20, 10))

        if self.role == "host":
            tk.Label(
                header,
                text="Password: " + self.room_password,
                bg=NAVY,
                fg="#C7D2FE",
                font=("Segoe UI", 11, "bold")
            ).pack(side="left", padx=(10, 20))

        tk.Button(header, text="Copy invite", bg="#334155", fg="white",
            relief="flat", command=self.copy_invite).pack(side="left", padx=5)
        self.theme_button = tk.Button(
            header, text="☾", command=self.toggle_dark_mode,
            bg="#334155", fg="#FFFFFF", activebackground="#475569",
            activeforeground="#FFFFFF", relief="flat", bd=0,
            font=("Segoe UI Symbol", 17), cursor="hand2", padx=9
        )
        self.theme_button.pack(side="right", padx=(4, 6))
        self.bind_tooltip(self.theme_button, "Toggle dark / light mode")
        self.connection_pill = tk.Label(header, text="● Connected", bg="#065F46", fg="white",
            font=("Segoe UI", 9, "bold"), padx=9, pady=5)
        self.connection_pill.pack(side="right", padx=8)
        tk.Label(header, text=f"{self.server_ip}:{self.server_port}", bg=NAVY,
            fg="#CBD5E1", font=("Segoe UI", 9)).pack(side="left", padx=8)
        tk.Label(
            header,
            text=self.username + "  •  " + self.role.title(),
            bg=NAVY,
            fg=WHITE,
            font=("Segoe UI", 10)
        ).pack(side="right", padx=20)

        toolbar = ttk.Frame(
            self.root,
            style="Toolbar.TFrame",
            padding=9
        )
        self.board_toolbar = toolbar
        toolbar.pack(
            fill="x",
            padx=8,
            pady=(8, 3)
        )

        # Toggle the entire left tool rail with a hamburger button.
        self.tools_menu_button = tk.Button(
            toolbar, text="☰", command=self.toggle_tool_rail,
            bg="#E2E8F0", fg="#17243B", relief="flat",
            font=("Segoe UI", 15, "bold"), padx=10, pady=0,
            cursor="hand2"
        )
        self.tools_menu_button.pack(side="left", padx=(3, 8))
        self.bind_tooltip(self.tools_menu_button, "Show or hide drawing tools")

        # Session actions live in the top bar; tools live in the left rail.
        self.tool_var = tk.StringVar(value=self.tool)
        self.size = tk.IntVar(value=3)
        ttk.Label(toolbar, text="Session", style="Toolbar.TLabel").pack(side="left", padx=7)
        self.online_buttons = []
        self.owner_buttons = []

        self.online_buttons = []
        self.owner_buttons = []

        for label, action, button_style in [
            ("Undo", "undo", "Soft.TButton"),
            ("Redo", "redo", "Soft.TButton"),
            ("Save", "save", "Success.TButton"),
            ("Clear", "clear", "Danger.TButton")
        ]:

            button = ttk.Button(
                toolbar,
                text=label,
                style=button_style,
                command=lambda a=action: self.send_action(a)
            )
            button.pack(side="left", padx=3)

            self.online_buttons.append(button)
            self.bind_tooltip(button, {"undo":"Undo last drawing", "redo":"Redo last drawing", "save":"Save whiteboard", "clear":"Clear board"}[action])

            if action == "clear":
                self.owner_buttons.append(button)

        ttk.Button(toolbar, text="PNG", command=lambda: self.export_whiteboard("png")).pack(side="left", padx=3)
        ttk.Button(toolbar, text="PDF", command=lambda: self.export_whiteboard("pdf")).pack(side="left", padx=3)
        self.more_button = ttk.Menubutton(toolbar, text="More ▾")
        more = tk.Menu(self.more_button, tearoff=False)
        more.add_command(label="Insert image", command=self.insert_image)
        more.add_command(label="Grid on/off", command=self.toggle_grid)
        more.add_command(label="Snapshots", command=self.snapshot_dialog)
        self.more_button["menu"] = more
        self.more_button.pack(side="left", padx=5)
        self.hand_button = tk.Button(toolbar, text="Raise Hand", command=self.raise_hand,
            bg="#E5E7EB", fg="#111827", relief="flat", padx=10, pady=5)
        self.hand_button.pack(side="left", padx=4)
        self.update_hand_button()

        button = tk.Button(
            toolbar, text="Lock", command=self.toggle_lock,
            bg="#16A34A", fg="white", activebackground="#15803D",
            relief="flat", padx=12, pady=5,
            font=("Segoe UI", 10, "bold")
        )
        button.pack(side="left", padx=3)
        self.lock_button = button
        self.update_lock_button()

        self.online_buttons.append(button)
        self.owner_buttons.append(button)

        ttk.Label(toolbar, text="Size", style="Toolbar.TLabel").pack(side="left", padx=(12, 4))
        self.size_spinbox = tk.Spinbox(
            toolbar, from_=1, to=30, increment=1, width=4,
            textvariable=self.size, font=("Segoe UI", 10), justify="center",
            command=self.refresh_size_preview,
            validate="key",
            validatecommand=(self.root.register(
                lambda value: value == "" or (value.isdigit() and 1 <= int(value) <= 30)
            ), "%P")
        )
        self.size_spinbox.pack(side="left", padx=(0, 5))
        self.size_spinbox.bind("<FocusOut>", self.normalize_brush_size)
        self.size_spinbox.bind("<Return>", self.normalize_brush_size)
        self.size_preview = tk.Canvas(toolbar, width=35, height=30,
            bg="#F8FAFC", highlightthickness=0)
        self.size_preview.pack(side="left")
        self.size.trace_add("write", lambda *_: self.refresh_size_preview())
        self.refresh_size_preview()

        status_bar = ttk.Frame(
            self.root,
            padding=(12, 5)
        )
        status_bar.pack(fill="x")
        self.board_statusbar = status_bar

        self.status = ttk.Label(
            status_bar,
            text="Connected"
        )
        self.status.pack(side="left")

        self.pending_label = ttk.Label(
            status_bar
        )
        self.pending_label.pack(side="right")

        main = ttk.Frame(
            self.root,
            padding=(8, 4, 8, 8)
        )
        main.pack(fill="both", expand=True)
        self.board_main = main

        side = ttk.Frame(
            main,
            width=275,
            padding=12,
            style="Dark.TFrame"
        )
        self.board_sidebar = side
        side.pack(
            side="right",
            fill="y",
            padx=(8, 0)
        )
        side.pack_propagate(False)

        # The tool rail can be hidden without destroying its buttons or state.
        self.tool_rail_visible = True
        rail = tk.Frame(main, bg="#E2E8F0", width=108)
        self.tool_rail = rail
        rail.pack(side="left", fill="y", padx=(0, 7))
        rail.pack_propagate(False)
        groups = [
            ("DRAW", [("✎", "pen", "P"), ("∿", "freehand", ""), ("▰", "marker", ""), ("◌", "highlighter", ""),
                      ("⌫", "eraser", "E"), ("✧", "laser", "")]),
            ("SHAPES", [("╱", "line", "L"), ("□", "rectangle", "R"),
                        ("◯", "circle", ""), ("⬭", "oval", ""), ("△", "triangle", "")]),
            ("OBJECTS", [("↖", "select", ""), ("T", "text", "T"),
                         ("▤", "sticky note", ""), ("▧", "image", "")])]
        # Reserve a permanent bottom area for colors and brush size.
        palette = tk.Frame(rail, bg="#E2E8F0")
        palette.pack(side="bottom", fill="x")
        tk.Label(palette, text="COLORS", bg="#E2E8F0", fg="#475569",
            font=("Segoe UI", 8, "bold")).pack(pady=(4, 2))
        self.swatches = tk.Frame(palette, bg="#E2E8F0")
        self.swatches.pack()
        self.refresh_swatches()
        self.color_button = tk.Button(
            palette, text="Color", command=self.choose_color, relief="solid",
            bd=2, font=("Segoe UI", 9, "bold"), padx=6, pady=4,
            cursor="hand2"
        )
        self.color_button.pack(pady=3, fill="x", padx=5)
        self.update_color_button()

        # Scroll the tools when the window is short; never hide the Color button.
        tool_holder = tk.Frame(rail, bg="#E2E8F0")
        tool_holder.pack(side="top", fill="both", expand=True)
        tool_canvas = tk.Canvas(tool_holder, bg="#E2E8F0", highlightthickness=0, bd=0)
        tool_scroll = tk.Scrollbar(tool_holder, orient="vertical", command=tool_canvas.yview)
        tool_canvas.configure(yscrollcommand=tool_scroll.set)
        tool_canvas.pack(side="left", fill="both", expand=True)
        tool_scroll.pack(side="right", fill="y")
        tool_content = tk.Frame(tool_canvas, bg="#E2E8F0")
        tool_window = tool_canvas.create_window((0, 0), window=tool_content, anchor="nw")
        tool_content.bind("<Configure>", lambda e: tool_canvas.configure(scrollregion=tool_canvas.bbox("all")))
        tool_canvas.bind("<Configure>", lambda e: tool_canvas.itemconfigure(tool_window, width=e.width))
        for heading, items in groups:
            tk.Label(tool_content, text=heading, bg="#E2E8F0", fg="#475569",
                font=("Segoe UI", 8, "bold")).pack(pady=(6, 1))
            for symbol, tool, shortcut in items:
                btn = tk.Button(tool_content, text=f"{symbol}  {tool.title()[:9]}",
                    anchor="w", relief="flat", bg="#E2E8F0", fg="#17243B",
                    font=("Segoe UI", 9), padx=4, pady=2,
                    command=lambda t=tool: self.activate_tool(t))
                btn.pack(fill="x", padx=2, pady=1)
                self.tool_buttons[tool] = btn
                self.bind_tooltip(btn, tool.title())
        self.refresh_tool_rail()

        canvas_frame = ttk.Frame(main)
        self.canvas_frame = canvas_frame
        canvas_frame.pack(
            side="left",
            fill="both",
            expand=True
        )

        self.canvas = tk.Canvas(
            canvas_frame,
            bg=WHITE,
            cursor="crosshair",
            highlightthickness=1,
            highlightbackground="#CBD5E1",
            scrollregion=(
                0, 0,
                self.board_width,
                self.board_height
            )
        )

        self.vscroll = ttk.Scrollbar(
            canvas_frame,
            orient="vertical",
            command=self.scroll_vertical_to
        )

        self.hscroll = ttk.Scrollbar(
            canvas_frame,
            orient="horizontal",
            command=self.canvas.xview
        )

        self.canvas.configure(
            yscrollcommand=self.vscroll.set,
            xscrollcommand=self.hscroll.set
        )

        self.vscroll.pack(
            side="right",
            fill="y"
        )

        self.hscroll.pack(
            side="bottom",
            fill="x"
        )

        self.canvas.pack(
            side="left",
            fill="both",
            expand=True
        )

        self.root.bind("<Delete>", self.delete_selected_text)
        self.root.bind("<BackSpace>", self.delete_selected_text)

        self.canvas.bind(
            "<Button-1>", self.start
        )
        self.canvas.bind(
            "<Double-Button-1>", self.double_click_object
        )
        self.canvas.bind(
            "<B1-Motion>", self.draw
        )
        self.canvas.bind(
            "<ButtonRelease-1>", self.finish
        )
        self.canvas.bind(
            "<Motion>", self.send_cursor
        )
        self.canvas.bind(
            "<Leave>", self.hide_cursor
        )
        self.canvas.bind(
            "<Configure>",
            lambda e: self.redraw()
        )
        self.canvas.bind(
            "<MouseWheel>", self.mouse_scroll
        )
        self.canvas.bind(
            "<Shift-MouseWheel>",
            self.horizontal_scroll
        )
        self.canvas.bind(
            "<Button-4>",
            lambda e: self.scroll_units(-3)
        )
        self.canvas.bind(
            "<Button-5>",
            lambda e: self.scroll_units(3)
        )

        ttk.Label(
            side,
            text="Participants",
            style="DarkTitle.TLabel"
        ).pack(anchor="w", pady=(0, 10))

        self.users = tk.Listbox(
            side,
            height=7,
            exportselection=False,
            bg=PANEL,
            fg=WHITE,
            selectbackground=BLUE,
            selectforeground=WHITE,
            relief="flat",
            borderwidth=0,
            font=("Segoe UI", 10)
        )
        self.users.pack(fill="x", pady=5)

        self.users.bind("<Button-3>", self.participant_context_menu)
        self.users.bind("<Button-2>", self.participant_context_menu)

        self.meeting_buttons = ttk.Frame(
            side,
            style="Dark.TFrame"
        )
        self.meeting_buttons.pack(
            side="bottom",
            fill="x"
        )

        chat_input = ttk.Frame(
            side,
            style="Dark.TFrame"
        )
        chat_input.pack(
            side="bottom",
            fill="x",
            pady=8
        )

        self.message = ttk.Entry(chat_input)
        self.message.pack(fill="x", pady=5)

        self.message.bind(
            "<Return>",
            lambda e: self.send_chat()
        )

        ttk.Button(
            chat_input,
            text="Send Message",
            style="Success.TButton",
            command=self.send_chat
        ).pack(fill="x")

        chat_header = tk.Frame(side, bg=NAVY)
        chat_header.pack(fill="x", pady=(15, 8))
        self.chat_toggle = tk.Button(chat_header, text="Group Chat ▾", command=self.toggle_chat,
            bg=NAVY, fg=WHITE, relief="flat", anchor="w")
        self.chat_toggle.pack(side="left", fill="x", expand=True)
        self.chat_settings_button = tk.Button(chat_header, text="⚙", bg=NAVY, fg=WHITE,
            relief="flat", command=self.open_chat_settings, font=("Segoe UI", 13))
        self.chat_settings_button.pack(side="right")
        self.refresh_chat_settings_button()

        self.chat = tk.Text(
            side,
            state="disabled",
            wrap="word",
            bg=PANEL,
            fg="#F8FAFC",
            insertbackground=WHITE,
            selectbackground=BLUE,
            relief="flat",
            borderwidth=0,
            padx=12,
            pady=12,
            font=("Segoe UI", 10)
        )
        self.chat.pack(
            fill="both",
            expand=True
        )

        self.update_buttons()
        self.redraw()
        self.redraw_chat()
        self.start_ping_loop()
        self.root.after(1200, self.retry_pending_sync)
        # Install a high-priority binding tag on every board widget.  Unlike
        # an all-only binding, this runs before ttk buttons consume key events.
        self.root.after_idle(lambda: self.canvas.focus_set() if self.page == "board" else None)
        if self.dark_mode:
            self.root.after_idle(self.apply_board_theme)

    # ---------- INTERFACE HELPERS ----------

    def toast(self, message, level="info"):
        if self.page != "board":
            if self.toast_timer:
                try:
                    self.root.after_cancel(self.toast_timer)
                except tk.TclError:
                    pass
            if self.toast_widget:
                try:
                    self.toast_widget.destroy()
                except tk.TclError:
                    pass
            color = {"error": "#BE123C", "success": "#047857", "info": "#334155"}.get(level, "#334155")
            self.toast_widget = tk.Label(self.root, text=str(message), bg=color, fg="white",
                padx=18, pady=10, font=("Segoe UI", 10, "bold"))
            self.toast_widget.place(relx=.5, rely=.86, anchor="center")
            self.toast_widget.lift()
            self.toast_timer = self.root.after(3000, self.dismiss_toast)
            return
        if self.toast_timer:
            try:
                self.root.after_cancel(self.toast_timer)
            except tk.TclError:
                pass
        if self.toast_widget:
            self.toast_widget.destroy()
        color = {"error": "#BE123C", "success": "#047857", "info": "#334155"}.get(level, "#334155")
        self.toast_widget = tk.Label(self.root, text=str(message), bg=color, fg="white",
            padx=18, pady=10, font=("Segoe UI", 10, "bold"))
        self.toast_widget.place(relx=.5, rely=.94, anchor="center")
        self.toast_widget.lift()
        self.toast_timer = self.root.after(2200, self.dismiss_toast)

    def dismiss_toast(self):
        if self.toast_widget:
            try:
                self.toast_widget.destroy()
            except tk.TclError:
                pass
        self.toast_widget = None
        self.toast_timer = None

    def copy_invite(self):
        invite = f"White Board\nServer: {self.server_ip}:{self.server_port}\nRoom ID: {self.room}\nPassword: {self.room_password}"
        self.root.clipboard_clear()
        self.root.clipboard_append(invite)
        self.toast("Invite copied to clipboard", "success")

    def install_keyboard_shortcuts(self):
        # Ctrl+Z, Ctrl+Y and Ctrl+S shortcuts intentionally disabled.
        # Toolbar buttons remain the supported Undo, Redo and Save controls.
        pass

    def update_color_button(self):
        button = getattr(self, "color_button", None)
        if button is not None and button.winfo_exists():
            button.configure(bg=self.color, fg=self.color_text(self.color),
                             activebackground=self.color,
                             activeforeground=self.color_text(self.color))

    def activate_tool(self, tool):
        if tool == "image":
            self.insert_image()
            return
        self.tool_var.set(tool)
        self.select_tool()

    def toggle_tool_rail(self):
        if self.page != "board" or not hasattr(self, "tool_rail"):
            return
        if self.tool_rail_visible:
            self.tool_rail.pack_forget()
            self.tool_rail_visible = False
        else:
            self.tool_rail.pack(side="left", fill="y", padx=(0, 7),
                                before=self.canvas_frame)
            self.tool_rail_visible = True
        self.tools_menu_button.configure(
            bg="#4F46E5" if self.tool_rail_visible else "#E2E8F0",
            fg="white" if self.tool_rail_visible else "#17243B"
        )

    def refresh_tool_rail(self):
        for tool, button in self.tool_buttons.items():
            button.configure(bg="#4F46E5" if tool == self.tool else "#E2E8F0",
                fg="white" if tool == self.tool else "#17243B")

    def bind_tooltip(self, widget, label):
        # Show a single non-blocking tooltip after the pointer rests on a button.
        # Keep its window alive while the mouse is over the button.
        def hide(event=None):
            after_id = getattr(widget, "_tooltip_after", None)
            if after_id is not None:
                try:
                    widget.after_cancel(after_id)
                except tk.TclError:
                    pass
                widget._tooltip_after = None
            tip = getattr(widget, "_tooltip", None)
            if tip is not None:
                try:
                    tip.destroy()
                except tk.TclError:
                    pass
                widget._tooltip = None

        def display():
            widget._tooltip_after = None
            if not widget.winfo_exists() or getattr(widget, "_tooltip", None) is not None:
                return
            tip = tk.Toplevel(widget)
            tip.wm_overrideredirect(True)
            try:
                tip.wm_attributes("-topmost", True)
            except tk.TclError:
                pass
            tk.Label(tip, text=label, bg="#17243B", fg="white",
                     font=("Segoe UI", 9), padx=8, pady=5).pack()
            tip.update_idletasks()
            x = widget.winfo_pointerx() + 12
            y = widget.winfo_pointery() + 18
            tip.wm_geometry(f"+{x}+{y}")
            widget._tooltip = tip

        def show(event=None):
            hide()
            widget._tooltip_after = widget.after(350, display)

        widget.bind("<Enter>", show, add="+")
        widget.bind("<Leave>", hide, add="+")
        widget.bind("<ButtonPress>", hide, add="+")

    def remember_color(self, color):
        self.recent_colors = [color] + [c for c in self.recent_colors if c != color]
        self.recent_colors = self.recent_colors[:5]
        self.refresh_swatches()
        self.refresh_size_preview()
        self.update_color_button()

    def refresh_swatches(self):
        if not hasattr(self, "swatches"):
            return
        for child in self.swatches.winfo_children():
            child.destroy()
        for color in self.recent_colors:
            tk.Button(self.swatches, bg=color, width=1, height=1, relief="solid",
                bd=2 if color == self.color else 0,
                command=lambda c=color: self.set_color(c)).pack(side="left", padx=0)

    def set_color(self, color):
        self.color = color
        self.remember_color(color)

    def normalize_brush_size(self, event=None):
        try:
            value = max(1, min(30, int(self.size_spinbox.get())))
        except (ValueError, tk.TclError):
            value = 3
        self.size.set(value)
        self.refresh_size_preview()

    def refresh_size_preview(self):
        if not hasattr(self, "size_preview"):
            return
        try:
            radius = max(1, min(15, self.size.get() / 2))
        except (ValueError, tk.TclError):
            return
        self.size_preview.delete("all")
        self.size_preview.create_oval(17-radius, 15-radius, 17+radius, 15+radius,
            fill=self.color, outline="")

    def update_connection_pill(self):
        if self.page != "board" or not hasattr(self, "connection_pill"):
            return
        if self.connected:
            label, bg = "Connected", "#047857"
        elif self.reconnecting:
            label, bg = "Reconnecting…", "#B45309"
        else:
            label, bg = "Offline", "#BE123C"
        ping = f" · {self.last_ping} ms" if self.connected and self.last_ping is not None else ""
        self.connection_pill.configure(text=f"● {label} · {len(self.pending)} pending{ping}", bg=bg)

    def start_ping_loop(self):
        if self.page != "board" or self.closing:
            return
        if self.connected:
            nonce = uuid.uuid4().hex
            self.ping_sent[nonce] = time.monotonic()
            if len(self.ping_sent) > 8:
                self.ping_sent.clear()
            self.send({"type": "ping", "nonce": nonce})
        self.update_connection_pill()
        self.root.after(3000, self.start_ping_loop)

    def participant_context_menu(self, event):
        if not (self.role == "host" or self.owner) or not self.connected:
            return
        idx = self.users.nearest(event.y)
        if idx < 0 or idx >= len(self.participants):
            return
        self.users.selection_clear(0, "end")
        self.users.selection_set(idx)
        name = self.participants[idx]
        if name in (self.username, self.meeting_owner):
            return
        menu = tk.Menu(self.root, tearoff=False)
        menu.add_command(label="Remove " + name, command=self.remove_participant)
        menu.tk_popup(event.x_root, event.y_root)

    def add_system_line(self, message):
        if self.page != "board":
            return
        self.chat_history.append({"system": True, "text": message})
        if self.chat_collapsed:
            self.unread += 1
            self.refresh_chat_toggle()
        self.redraw_chat()

    def refresh_chat_toggle(self):
        if hasattr(self, "chat_toggle"):
            self.chat_toggle.configure(text=("Group Chat ▸" if self.chat_collapsed else "Group Chat ▾") +
                (f" ({self.unread})" if self.unread else ""))

    def toggle_chat(self):
        self.chat_collapsed = not self.chat_collapsed
        if self.chat_collapsed:
            self.chat.pack_forget()
        else:
            self.chat.pack(fill="both", expand=True)
            self.unread = 0
        self.refresh_chat_toggle()

    # ---------- SCROLLING ----------

    def mouse_scroll(self, event):

        if self.page == "board":
            self.scroll_units(
                -3 if event.delta > 0 else 3
            )

    def scroll_units(self, amount):

        if self.page != "board":
            return

        if amount > 0:

            self.expand_whiteboard(
                self.canvas.canvasy(
                    self.canvas.winfo_height()
                ) + 700
            )

        self.canvas.yview_scroll(
            amount, "units"
        )
        self.root.after_idle(self.refresh_below_indicators)

    def scroll_vertical_to(self, *args):
        self.canvas.yview(*args)
        self.root.after_idle(self.refresh_below_indicators)

    def horizontal_scroll(self, event):

        if self.page == "board":

            self.canvas.xview_scroll(
                -3 if event.delta > 0 else 3,
                "units"
            )

    def expand_whiteboard(self, y):

        if self.page != "board":
            return

        if y >= self.board_height - 500:

            new_height = min(
                self.max_height,
                max(
                    self.board_height + self.expand_amount,
                    int(y) + 1000
                )
            )

            if new_height > self.board_height:

                self.board_height = new_height

                self.canvas.configure(
                    scrollregion=(
                        0, 0,
                        self.board_width,
                        self.board_height
                    )
                )

    def expand_for_stroke(self, stroke):

        points = stroke.get(
            "points", [0, 0, 0, 0]
        )

        self.expand_whiteboard(
            max(points[1], points[3])
        )

    def canvas_position(self, event):

        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)

        self.expand_whiteboard(y)

        return x, y

    # ---------- DRAWING ----------

    def select_tool(self, event=None):

        if self.start_point and self.tool in SHAPES:

            self.send_shape_preview(
                [*self.start_point, *self.start_point],
                visible=False,
                force=True
            )

        self.tool = self.tool_var.get()
        self.refresh_tool_rail()
        if self.tool != "text":
            self.selected_text = None
        if self.tool != "select":
            self.selected_object = None
            self.object_drag = None
            self.update_text_selection()
        if self.tool != "laser":
            self.hide_local_laser()
        if self.tool != "select":
            self.canvas.delete("object_selection")
        self.canvas.configure(cursor="none" if self.tool == "laser" else "crosshair")
        self.start_point = None
        self.last = None
        self.text_drag = None
        self.text_drag_mode = None

        if self.preview is not None:

            self.canvas.delete(self.preview)
            self.preview = None

    def color_text(self, hex_color):

        color = hex_color.lstrip("#")

        r = int(color[0:2], 16)
        g = int(color[2:4], 16)
        b = int(color[4:6], 16)

        brightness = (
            r*299 + g*587 + b*114
        ) / 1000

        return (
            "black" if brightness > 155
            else "white"
        )

    def choose_color(self):

        result = colorchooser.askcolor(
            color=self.color, parent=self.root, title="Choose drawing color"
        )

        if result[1]:

            self.color = result[1]
            text_color = self.color_text(self.color)

            self.remember_color(self.color)

    def lighten(self, color):

        rgb = [
            int(color[i:i+2], 16)
            for i in (1, 3, 5)
        ]

        rgb = [
            int(v*.35 + 255*.65)
            for v in rgb
        ]

        return "#" + "".join(
            f"{v:02x}" for v in rgb
        )

    def start(self, event):

        # Canvas needs keyboard focus after a drawing click (especially on Windows).
        self.canvas.focus_set()
        self.send_cursor(event, force=True)

        if self.tool == "laser":
            return

        if self.locked and self.role != "host" and not self.owner:
            return

        x, y = self.canvas_position(event)

        # Existing shapes, images and sticky notes can be dragged directly.
        # Respect the same ownership and lock rules as the Select tool.
        self.direct_object_drag = False
        if self.tool != "select":
            grabbed = self.find_object(x, y, kinds=SHAPES | {"image", "sticky_note"})
            if grabbed:
                self.selected_object = grabbed["id"]
                self.object_drag = (x, y, list(grabbed["points"]), "move")
                self.direct_object_drag = True
                self.start_point = (x, y)
                self.last = (x, y)
                self.show_object_preview(grabbed["points"])
                return
        if self.grid_visible and self.tool in SHAPES:
            x, y = round(x / 50) * 50, round(y / 50) * 50
        self.start_point = (x, y)
        self.last = (x, y)
        self.active_stroke_group = uuid.uuid4().hex if self.tool in FREE else None

        if self.tool == "select":
            found = self.find_object(x, y)
            self.selected_object = found.get("id") if found else None
            self.object_drag = None
            if found:
                a,b,c,d = found["points"]
                corners = [(a,b,"nw"),(c,b,"ne"),(a,d,"sw"),(c,d,"se")]
                nearest = min(corners, key=lambda p:(x-p[0])**2+(y-p[1])**2)
                mode = "resize_" + nearest[2] if abs(x-nearest[0]) <= 14 and abs(y-nearest[1]) <= 14 else "move"
                self.object_drag = (x, y, list(found["points"]), mode)
            self.update_object_selection()
            return

        if self.tool == "sticky note":
            self.add_sticky_note(x, y)
            self.start_point = None
            self.last = None
            return

        if self.tool == "text":
            # Corner handles take precedence over the text body.
            handle = self.find_text_handle(x, y)
            selected = self.selected_text if handle else self.find_text_at(x, y)
            if selected:
                state = self.text_state(selected)
                if state:
                    self.selected_text = selected
                    self.text_drag = (x, y, state[0][0], state[0][1], state[1])
                    self.text_resize_origin = self.canvas.bbox(self.canvas.find_withtag("textid_" + selected)[0])
                    self.text_drag_mode = "resize" if handle else "move"
                    self.update_text_selection()
                    return
            self.selected_text = None
            self.text_drag = None
            self.text_drag_mode = None
            self.update_text_selection()
            text = simpledialog.askstring("Text", "Enter text:", parent=self.root)
            if text:
                self.add_stroke("text", [x, y, x, y], text=text[:500])
            self.start_point = None

        elif self.tool in SHAPES:

            self.send_shape_preview(
                [x, y, x, y],
                force=True
            )

    def double_click_object(self, event):
        if self.locked and self.role != "host" and not self.owner:
            return "break"
        x, y = self.canvas_position(event)
        found = self.find_object(x, y, kinds=SHAPES | {"image", "sticky_note"})
        if found is None:
            return
        # Select mode exposes all four resize handles immediately.
        self.direct_object_drag = False
        self.object_drag = None
        self.start_point = None
        self.last = None
        self.selected_object = found["id"]
        self.tool_var.set("select")
        self.select_tool()
        self.selected_object = found["id"]
        self.update_object_selection()
        return "break"

    def draw(self, event):

        self.send_cursor(event)

        if self.tool == "laser":
            return

        if (self.locked and self.role != "host" and not self.owner) or self.start_point is None:
            return

        x1, y1 = self.start_point
        x2, y2 = self.canvas_position(event)
        if self.grid_visible and self.tool in SHAPES:
            x2, y2 = round(x2 / 50) * 50, round(y2 / 50) * 50

        if self.tool == "select" or getattr(self, "direct_object_drag", False):
            if self.object_drag and self.selected_object:
                sx, sy, original, mode = self.object_drag
                dx, dy = x2 - sx, y2 - sy
                new = self.object_drag_bounds(original, dx, dy, mode)
                self.show_object_preview(new)
            return

        if self.tool == "text" and self.text_drag:
            sx, sy, ox, oy, original_width = self.text_drag
            items = self.canvas.find_withtag("textid_" + self.selected_text)
            if items:
                item = items[0]
                if self.text_drag_mode == "move":
                    self.canvas.coords(item, max(0, ox + x2 - sx), max(0, oy + y2 - sy))
                else:
                    # Resize proportionally by dragging any corner away from/toward the center.
                    bounds = self.text_resize_origin
                    if bounds:
                        bx1, by1, bx2, by2 = bounds
                        center_x, center_y = (bx1 + bx2)/2, (by1 + by2)/2
                        old_radius = max(10, ((sx-center_x)**2 + (sy-center_y)**2)**0.5)
                        new_radius = ((x2-center_x)**2 + (y2-center_y)**2)**0.5
                        new_width = max(1, min(50, round(original_width * new_radius / old_radius)))
                        self.canvas.itemconfigure(item, font=("Segoe UI", max(12, int(new_width)*4)))
                self.update_text_selection()
                self.send_text_preview(item)
            return

        if self.tool in FREE:

            x, y = self.last

            if (x, y) == (x2, y2):
                return

            self.add_stroke(
                self.tool,
                [x, y, x2, y2]
            )

            self.last = (x2, y2)

        elif self.tool in SHAPES:

            if self.preview is not None:
                self.canvas.delete(self.preview)

            points = [x1, y1, x2, y2]

            self.preview = self.draw_shape(
                self.tool,
                points,
                self.color,
                self.size.get()
            )

            self.send_shape_preview(points)

            self.canvas.tag_raise(
                "remote_cursor"
            )

    def finish(self, event):

        self.send_cursor(event, force=True)

        if self.tool == "laser":
            return

        if self.start_point is None:
            return

        x, y = self.canvas_position(event)
        if self.grid_visible and self.tool in SHAPES:
            x, y = round(x / 50) * 50, round(y / 50) * 50

        if self.tool == "select" or getattr(self, "direct_object_drag", False):
            if self.object_drag and self.selected_object:
                sx, sy, original, mode = self.object_drag
                dx, dy = x - sx, y - sy
                new = self.object_drag_bounds(original, dx, dy, mode)
                if new != original:
                    self.modify_object(self.selected_object,new)
            self.object_drag = None
            self.direct_object_drag = False
            self.start_point = None
            self.last = None
            self.redraw()
            return

        if self.tool == "text" and self.text_drag:
            sx, sy, ox, oy, original_width = self.text_drag
            mode = self.text_drag_mode
            self.send_text_preview(visible=False, force=True)
            self.text_drag = None
            self.text_drag_mode = None
            items = self.canvas.find_withtag("textid_" + self.selected_text)
            if items:
                item = items[0]
                if mode == "move":
                    nx, ny = self.canvas.coords(item)[:2]
                    if abs(nx - ox) > 0.5 or abs(ny - oy) > 0.5:
                        self.edit_text(self.selected_text, nx, ny)
                elif mode == "resize":
                    import tkinter.font as tkfont
                    font = tkfont.Font(font=self.canvas.itemcget(item, "font"))
                    new_width = max(1, min(50, round(abs(font.cget("size"))/4)))
                    if new_width != original_width:
                        self.edit_text(self.selected_text, ox, oy, new_width)
                self.update_text_selection()

        if self.tool in SHAPES:

            x1, y1 = self.start_point
            points = [x1, y1, x, y]

            if self.preview is not None:

                self.canvas.delete(self.preview)
                self.preview = None

            if (x1, y1) != (x, y):

                self.add_stroke(
                    self.tool, points
                )

            self.send_shape_preview(
                points,
                visible=False,
                force=True
            )

        self.start_point = None
        self.last = None
        self.active_stroke_group = None

    def add_stroke(self, shape, points, text=""):

        width = self.size.get()
        color = self.color

        if shape == "marker":
            width = max(width, 10)

        elif shape == "highlighter":
            width = max(width * 4, 22)
            width = min(width, 50)

        elif shape == "eraser":
            width = max(width, 18)
            color = WHITE

        stroke = {
            "type": "stroke",
            "id": uuid.uuid4().hex,
            "user": self.username,
            "shape": shape,
            "points": points,
            "color": color,
            "width": width
        }

        if shape == "text":
            stroke["text"] = text
        if shape in FREE and getattr(self, "active_stroke_group", None):
            stroke["group"] = self.active_stroke_group

        if shape != "eraser":
            self.strokes.append(stroke)
            self.expand_for_stroke(stroke)
            self.paint(stroke)
        self.queue_event(stroke)

    def add_sticky_note(self, x, y):
        """One note is one stroke: saved, synchronized, undoable and redoable."""
        dialog = tk.Toplevel(self.root)
        dialog.title("New Sticky Note")
        dialog.configure(bg=WHITE)
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text="Sticky Note", bg=WHITE, fg=TEXT,
                 font=("Segoe UI", 13, "bold")).pack(padx=20, pady=(16, 5))
        tk.Label(dialog, text="Write your note (max 500 characters)",
                 bg=WHITE, fg=MUTED).pack(padx=20)
        editor = tk.Text(dialog, width=36, height=7, wrap="word",
                         font=("Segoe UI", 11), relief="solid", bd=1)
        editor.pack(padx=20, pady=10)
        editor.focus_set()
        selected_color = tk.StringVar(value=self.color)
        color_button = tk.Button(dialog, text="Note color", bg=self.color,
                                 fg=self.color_text(self.color), relief="flat")
        def choose_note_color():
            chosen = colorchooser.askcolor(color=selected_color.get(), parent=dialog)[1]
            if chosen:
                selected_color.set(chosen)
                color_button.configure(bg=chosen, fg=self.color_text(chosen))
        color_button.configure(command=choose_note_color)
        color_button.pack(pady=(0, 8))
        def save_note():
            content = editor.get("1.0", "end-1c").strip()
            if not content:
                messagebox.showwarning("Sticky Note", "Please enter some text.", parent=dialog)
                return
            if len(content) > 500:
                messagebox.showwarning("Sticky Note", "Maximum 500 characters.", parent=dialog)
                return
            note_color = selected_color.get()
            dialog.destroy()
            stroke = {
                "type": "stroke", "id": uuid.uuid4().hex,
                "user": self.username, "shape": "sticky_note",
                "points": [x, y, x + 230, y + 170],
                "color": note_color, "width": 2, "text": content
            }
            self.strokes.append(stroke)
            self.expand_for_stroke(stroke)
            self.paint(stroke)
            self.queue_event(stroke)
        actions = tk.Frame(dialog, bg=WHITE)
        actions.pack(pady=(0, 16))
        tk.Button(actions, text="Cancel", command=dialog.destroy,
                  width=10).pack(side="left", padx=6)
        tk.Button(actions, text="Add Note", command=save_note,
                  bg=BLUE, fg=WHITE, width=10).pack(side="left", padx=6)
        dialog.bind("<Escape>", lambda e: dialog.destroy())
        self.root.wait_window(dialog)

    # Text edits are append-only stroke events. This preserves undo/redo,
    # reconnect merging, and existing saved whiteboards.
    def text_state(self, text_id):
        original = next((e for e in self.strokes
                         if e.get("id") == text_id and e.get("shape") == "text"), None)
        if original is None:
            return None
        points = list(original["points"])
        width = original["width"]
        deleted = False
        for event in self.strokes:
            if event.get("target") != text_id:
                continue
            if event.get("shape") == "text_edit":
                points = list(event["points"])
                width = event["width"]
            elif event.get("shape") == "text_delete":
                deleted = True
        return None if deleted else (points, width, original)

    def find_text_at(self, x, y):
        # Use the bounding box rather than only painted glyph pixels.
        # This also makes selecting short or narrow text easier.
        for item in reversed(self.canvas.find_all()):
            tags = self.canvas.gettags(item)
            text_ids = [tag[7:] for tag in tags if tag.startswith("textid_")]
            if not text_ids:
                continue
            bounds = self.canvas.bbox(item)
            if bounds and bounds[0]-4 <= x <= bounds[2]+4 and bounds[1]-4 <= y <= bounds[3]+4:
                text_id = text_ids[0]
                state = self.text_state(text_id)
                if state and state[2].get("user") == self.username:
                    return text_id
        return None

    def find_text_handle(self, x, y):
        if not self.selected_text:
            return None
        for item in self.canvas.find_withtag("text_resize_handle"):
            bounds = self.canvas.bbox(item)
            if bounds and bounds[0]-3 <= x <= bounds[2]+3 and bounds[1]-3 <= y <= bounds[3]+3:
                return True
        return None

    def update_text_selection(self):
        if self.page != "board":
            return
        self.canvas.delete("text_selection")
        if not self.selected_text or self.tool != "text":
            return
        items = self.canvas.find_withtag("textid_" + self.selected_text)
        if not items:
            return
        bounds = self.canvas.bbox(items[0])
        if bounds:
            x1, y1, x2, y2 = bounds
            self.canvas.create_rectangle(x1-4, y1-4, x2+4, y2+4,
                outline="#4F46E5", width=1, dash=(4, 3),
                tags=("text_selection",))
            for hx, hy in ((x1-4,y1-4),(x2+4,y1-4),(x1-4,y2+4),(x2+4,y2+4)):
                self.canvas.create_rectangle(hx-5,hy-5,hx+5,hy+5,
                    fill="white", outline="#4F46E5", width=2,
                    tags=("text_selection", "text_resize_handle"))
            self.canvas.tag_raise("text_selection")

    def edit_text(self, text_id, x, y, width=None):
        if (self.locked and self.role != "host" and not self.owner) or not self.connected or not text_id:
            return
        state = self.text_state(text_id)
        if state is None or state[2].get("user") != self.username:
            return
        points, old_width, original = state
        width = old_width if width is None else max(1, min(50, width))
        event = {
            "type": "stroke", "id": uuid.uuid4().hex,
            "user": self.username, "shape": "text_edit",
            "target": text_id, "points": [x, y, x, y],
            "color": original["color"], "width": width
        }
        self.strokes.append(event)
        self.paint(event)
        self.queue_event(event)
        self.update_text_selection()

    def delete_selected_text(self, event=None):
        # Do not hijack Backspace/Delete while typing in chat, login or dialogs.
        focused = self.root.focus_get()
        if isinstance(focused, (tk.Entry, tk.Text, ttk.Entry, ttk.Combobox, tk.Spinbox)):
            return
        if self.page == "board" and self.tool == "select" and self.selected_object:
            obj = next((o for o in self.active_objects() if o["id"] == self.selected_object), None)
            if obj:
                self.modify_object(obj["id"],obj["points"],delete=True)
                self.selected_object = None
                return "break"
        if (self.page != "board" or self.tool != "text" or
                not self.selected_text or (self.locked and self.role != "host" and not self.owner) or not self.connected):
            return
        target = self.selected_text
        state = self.text_state(target)
        if state is None or state[2].get("user") != self.username:
            return
        points, width, original = state
        deletion = {
            "type": "stroke", "id": uuid.uuid4().hex,
            "user": self.username, "shape": "text_delete",
            "target": target, "points": list(points),
            "color": original["color"], "width": width
        }
        self.strokes.append(deletion)
        self.selected_text = None
        self.text_drag = None
        self.text_drag_mode = None
        self.paint(deletion)
        self.update_text_selection()
        self.queue_event(deletion)
        return "break"

    # Live text edits are temporary, never added to strokes or undo history.
    def send_text_preview(self, item=None, visible=True, force=False):
        if not self.connected or self.page != "board" or not self.selected_text:
            return
        now = time.monotonic()
        if visible and not force and now - self.last_text_preview_send < .04:
            return
        self.last_text_preview_send = now
        if visible:
            if item is None:
                return
            import tkinter.font as tkfont
            font = tkfont.Font(font=self.canvas.itemcget(item, "font"))
            width = max(1, min(50, round(abs(font.cget("size"))/4)))
            x, y = self.canvas.coords(item)[:2]
        else:
            x = y = 0
            width = 1
        self.send({"type": "text_preview", "target": self.selected_text,
                   "x": x, "y": y, "width": width, "visible": visible})

    def show_text_preview(self, msg):
        name = msg.get("username", "")
        if not name or name == self.username or self.page != "board":
            return
        self.clear_text_preview(name)
        if not msg.get("visible", True):
            return
        target = msg.get("target", "")
        items = self.canvas.find_withtag("textid_" + target)
        if not items or not self.text_state(target):
            return
        item = items[0]
        self.remote_text_previews[name] = {
            "target": target, "x": msg["x"], "y": msg["y"], "width": msg["width"]
        }
        self.canvas.coords(item, msg["x"], msg["y"])
        self.canvas.itemconfigure(item, font=("Segoe UI", max(12, int(msg["width"])*4)))
        self.update_text_selection()

    def clear_text_preview(self, name):
        preview = self.remote_text_previews.pop(name, None)
        if not preview:
            return
        target = preview["target"]
        state = self.text_state(target)
        items = self.canvas.find_withtag("textid_" + target)
        if state and items:
            self.canvas.coords(items[0], state[0][0], state[0][1])
            self.canvas.itemconfigure(items[0], font=("Segoe UI", max(12, int(state[1])*4)))
        self.update_text_selection()

    def resize_text(self, change):
        if self.tool != "text" or not self.selected_text:
            return
        state = self.text_state(self.selected_text)
        if state:
            points, width, _ = state
            self.edit_text(self.selected_text, points[0], points[1], width + change)

    def draw_shape(self, shape, p, color, width):

        x1, y1, x2, y2 = p

        if shape == "line":

            return self.canvas.create_line(
                x1, y1, x2, y2,
                fill=color,
                width=width
            )

        if shape == "rectangle":

            return self.canvas.create_rectangle(
                x1, y1, x2, y2,
                outline=color,
                width=width
            )

        if shape == "oval":

            return self.canvas.create_oval(
                x1, y1, x2, y2,
                outline=color,
                width=width
            )

        if shape == "circle":

            side = min(
                abs(x2-x1),
                abs(y2-y1)
            )

            x2 = (
                x1+side if x2 >= x1
                else x1-side
            )

            y2 = (
                y1+side if y2 >= y1
                else y1-side
            )

            return self.canvas.create_oval(
                x1, y1, x2, y2,
                outline=color,
                width=width
            )

        if shape == "triangle":

            return self.canvas.create_polygon(
                (x1+x2)/2, y1,
                x1, y2,
                x2, y2,
                outline=color,
                fill="",
                width=width
            )

        return self.canvas.create_line(
            x1, y1, x2, y2,
            fill=color,
            width=width
        )

    def paint(self, stroke):

        shape = stroke["shape"]
        points = stroke["points"]
        color = stroke["color"]
        width = stroke["width"]

        if shape == "eraser":
            return None

        if shape in ("object_edit", "object_delete"):
            return None

        if shape == "image":
            try:
                from PIL import Image, ImageTk
                raw = base64.b64decode(stroke.get("image", ""), validate=True)
                picture = Image.open(io.BytesIO(raw)).convert("RGBA")
                x1,y1,x2,y2 = points
                picture.thumbnail((max(1,int(abs(x2-x1))), max(1,int(abs(y2-y1)))))
                picture = picture.resize((max(1,int(abs(x2-x1))),max(1,int(abs(y2-y1)))))
                photo = ImageTk.PhotoImage(picture, master=self.root)
                self.image_refs[stroke["id"]] = photo
                return self.canvas.create_image(x1,y1,anchor="nw",image=photo,
                    tags=("object_"+stroke["id"],))
            except Exception:
                return None

        if shape == "sticky_note":
            x1, y1, x2, y2 = points
            # Group canvas items with the note ID so redraw removes both.
            tag = "sticky_" + stroke["id"]
            self.canvas.create_rectangle(
                x1 + 4, y1 + 5, x2 + 4, y2 + 5,
                fill="#CBD5E1", outline="", tags=(tag,)
            )
            item = self.canvas.create_rectangle(
                x1, y1, x2, y2, fill=color,
                outline="#64748B", width=1, tags=(tag,)
            )
            self.canvas.create_text(
                x1 + 16, y1 + 22, anchor="nw",
                text=stroke.get("text", ""),
                fill=self.color_text(color),
                font=("Arial", 12), width=max(50, x2-x1-32),
                tags=(tag, "sticky_note_text")
            )
            self.canvas.tag_raise("sticky_note_text")
        elif shape == "text_delete":
            self.canvas.delete("textid_" + stroke.get("target", ""))
            return None

        if shape == "text_edit":
            target = stroke.get("target", "")
            items = self.canvas.find_withtag("textid_" + target)
            if items:
                item = items[0]
                self.canvas.coords(item, points[0], points[1])
                self.canvas.itemconfigure(item, font=("Segoe UI", max(12, int(width)*4)))
            else:
                return None

        elif shape == "text":

            item = self.canvas.create_text(
                points[0],
                points[1],
                text=stroke.get("text", ""),
                fill=color,
                font=(
                    "Segoe UI",
                    max(12, int(width)*4)
                ),
                anchor="nw",
                tags=("textid_" + stroke["id"],)
            )

        elif shape in FREE:

            if shape == "highlighter":
                item = self.canvas.create_line(
                    *points, fill=color, width=width,
                    capstyle="round", smooth=True,
                    stipple="gray50", tags=("highlighter_stroke",)
                )
                # Keep lettering readable even when highlighting is added later.
                self.canvas.tag_raise("sticky_note_text")
                for text_item in self.canvas.find_all():
                    if any(tag.startswith("textid_") for tag in self.canvas.gettags(text_item)):
                        self.canvas.tag_raise(text_item)
            else:
                item = self.canvas.create_line(
                    *points,
                    fill=color,
                    width=width,
                    capstyle="round",
                    smooth=True
                )

        else:

            item = self.draw_shape(
                shape,
                points,
                color,
                width
            )

        self.canvas.tag_raise(
            "remote_preview"
        )
        self.canvas.tag_raise(
            "remote_cursor"
        )

        return item

    # ---------- ADVANCED WHITEBOARD FEATURES ----------

    def active_objects(self):
        erased = {t for e in self.strokes if e.get("shape") == "eraser" for t in e.get("targets", [])}
        deleted = {e.get("target") for e in self.strokes if e.get("shape") == "object_delete"}
        changes = {e.get("target"): e.get("points") for e in self.strokes if e.get("shape") == "object_edit"}
        for item in reversed(self.strokes):
            if item.get("shape") not in SHAPES | {"image", "sticky_note"}:
                continue
            if item["id"] in erased or item["id"] in deleted:
                continue
            result = dict(item)
            result["points"] = changes.get(item["id"], item["points"])
            yield result

    def find_object(self, x, y, kinds=None):
        for item in self.active_objects():
            if kinds is not None and item.get("shape") not in kinds:
                continue
            a,b,c,d = item["points"]
            if min(a,c)-9 <= x <= max(a,c)+9 and min(b,d)-9 <= y <= max(b,d)+9:
                if self.role == "host" or self.owner or item.get("user") == self.username:
                    return item
        return None

    def object_drag_bounds(self, original, dx, dy, mode):
        a,b,c,d = original
        if mode == "move":
            dx = max(-a, dx)
            dy = max(-b, dy)
            return [a+dx,b+dy,c+dx,d+dy]
        corner = mode.replace("resize_", "")
        minimum = 24
        if "w" in corner:
            a = max(0, min(a+dx, c-minimum))
        else:
            c = max(a+minimum, c+dx)
        if "n" in corner:
            b = max(0, min(b+dy, d-minimum))
        else:
            d = max(b+minimum, d+dy)
        return [a,b,c,d]

    def show_object_preview(self, points):
        self.canvas.delete("object_selection")
        x1,y1,x2,y2 = points
        self.canvas.create_rectangle(min(x1,x2),min(y1,y2),max(x1,x2),max(y1,y2),
            dash=(5,3),outline=BLUE,width=2,tags="object_selection")
        for px,py in ((x1,y1),(x2,y1),(x1,y2),(x2,y2)):
            self.canvas.create_rectangle(px-5,py-5,px+5,py+5,fill="white",
                outline=BLUE,width=2,tags="object_selection")

    def update_object_selection(self):
        self.canvas.delete("object_selection")
        if not self.selected_object or self.tool != "select":
            return
        for item in self.active_objects():
            if item["id"] == self.selected_object:
                self.show_object_preview(item["points"])
                return
        self.selected_object = None

    def modify_object(self, target, points, delete=False):
        item = next((e for e in self.active_objects() if e["id"] == target), None)
        if not item or (self.locked and self.role != "host" and not self.owner) or not self.connected:
            return
        event = {"type":"stroke", "id":uuid.uuid4().hex,"user":self.username,
                 "shape":"object_delete" if delete else "object_edit",
                 "target":target,"points":points,"color":item["color"],"width":item["width"]}
        self.strokes.append(event)
        self.queue_event(event)
        self.redraw()

    def insert_image(self):
        if self.page != "board" or (self.locked and self.role != "host" and not self.owner) or not self.connected:
            return
        try:
            from PIL import Image
        except ImportError:
            messagebox.showerror("Pillow required", "Install Pillow: python -m pip install pillow")
            return
        path = filedialog.askopenfilename(filetypes=[("Images", "*.png *.jpg *.jpeg")])
        if not path:
            return
        try:
            with Image.open(path) as src:
                img = src.convert("RGB")
                img.thumbnail((650, 500))
                buffer = io.BytesIO()
                img.save(buffer, "JPEG", quality=75, optimize=True)
            encoded = base64.b64encode(buffer.getvalue()).decode("ascii")
            if len(encoded) > 1300000:
                raise ValueError("Image is too large")
            x = self.canvas.canvasx(self.canvas.winfo_width()//2)
            y = self.canvas.canvasy(self.canvas.winfo_height()//2)
            event = {"type":"stroke","id":uuid.uuid4().hex,"user":self.username,
                "shape":"image","points":[x,y,x+img.width,y+img.height],
                "color":"#FFFFFF","width":1,"image":encoded}
            self.strokes.append(event)
            self.queue_event(event)
            self.tool_var.set("select")
            self.select_tool()
            self.selected_object = event["id"]
            self.redraw()
        except Exception as error:
            messagebox.showerror("Insert image failed", str(error))

    def draw_grid(self):
        # A local, non-exported visual guide; no extra shared strokes.
        for x in range(0, min(self.board_width, 10000)+1, 50):
            self.canvas.create_line(x,0,x,min(self.board_height,10000),fill="#334155" if self.dark_mode else "#E9EDF4",tags="grid")
        for y in range(0, min(self.board_height, 10000)+1, 50):
            self.canvas.create_line(0,y,min(self.board_width,10000),y,fill="#334155" if self.dark_mode else "#E9EDF4",tags="grid")
        self.canvas.tag_lower("grid")

    def toggle_grid(self):
        self.grid_visible = not self.grid_visible
        self.redraw()

    def update_hand_button(self):
        if self.hand_button is None or self.page != "board":
            return
        raised = self.username in self.raised_hands
        try:
            self.hand_button.configure(text="Lower Hand" if raised else "Raise Hand",
                bg="#FBBF24" if raised else "#E5E7EB",
                fg="#111827")
        except tk.TclError:
            pass

    def raise_hand(self):
        if self.page == "board" and self.connected:
            self.send({"type":"raise_hand"})

    def snapshot_dialog(self):
        if self.page != "board" or not self.connected:
            return
        if not self.owner:
            messagebox.showinfo("Snapshots", "Only the room owner can save or restore snapshots.")
            return
        self.send({"type":"snapshot_list"})

    def show_snapshots(self, items):
        dialog = tk.Toplevel(self.root)
        dialog.title("Whiteboard Version History")
        dialog.geometry("440x340")
        tk.Label(dialog,text="Saved snapshots (newest first)").pack(pady=8)
        lb = tk.Listbox(dialog)
        lb.pack(fill="both",expand=True,padx=12)
        for item in reversed(items):
            lb.insert("end", item.get("label", "Snapshot"))
        def create():
            label = simpledialog.askstring("Save Snapshot","Snapshot name:",parent=dialog)
            if label:
                self.send({"type":"snapshot_save","label":label})
                dialog.destroy()
        def restore():
            if not lb.curselection():
                return
            item = list(reversed(items))[lb.curselection()[0]]
            if messagebox.askyesno("Restore", "Restore this version for everyone?",parent=dialog):
                self.send({"type":"snapshot_restore","id":item["id"]})
                dialog.destroy()
        ttk.Button(dialog,text="Save Current Version",command=create).pack(pady=4)
        ttk.Button(dialog,text="Restore Selected Version",command=restore).pack(pady=4)

    def export_whiteboard(self, file_type):
        """Render the complete scrollable whiteboard, not a screen capture."""
        if self.page != "board":
            return
        try:
            from PIL import Image, ImageDraw, ImageFont
        except ImportError:
            messagebox.showerror("Pillow required", "Install Pillow: python -m pip install pillow")
            return

        extension = ".png" if file_type == "png" else ".pdf"
        selected = filedialog.asksaveasfilename(
            title="Export full whiteboard as " + file_type.upper(),
            defaultextension=extension,
            initialfile="whiteboard_" + self.room + extension,
            filetypes=[("PNG image", "*.png")] if file_type == "png" else [("PDF document", "*.pdf")]
        )
        if not selected:
            return
        try:
            import math
            import base64 as _base64
            import io as _io
            from PIL import Image, ImageDraw, ImageFont

            # Board dimensions are document coordinates, independent of scroll position.
            board_w = max(1, int(self.board_width))
            board_h = max(1, int(self.board_height))
            # Guard against accidentally allocating an enormous image.
            if board_w * board_h > 120000000:
                raise ValueError("Whiteboard too large for one image")
            background = "#101827" if self.dark_mode else "#FFFFFF"
            result = Image.new("RGB", (board_w, board_h), background)
            draw = ImageDraw.Draw(result)
            if self.grid_visible:
                grid_color = "#334155" if self.dark_mode else "#E9EDF4"
                for x in range(0, board_w, 50):
                    draw.line((x, 0, x, board_h), fill=grid_color)
                for y in range(0, board_h, 50):
                    draw.line((0, y, board_w, y), fill=grid_color)

            erased = {t for e in self.strokes if e.get("shape") == "eraser" for t in e.get("targets", [])}
            deleted = {e.get("target") for e in self.strokes if e.get("shape") in ("object_delete", "text_delete")}
            object_updates = {e.get("target"): e.get("points") for e in self.strokes if e.get("shape") == "object_edit"}
            text_updates = {e.get("target"): e for e in self.strokes if e.get("shape") == "text_edit"}

            def font(size):
                size = max(8, int(size))
                for candidate in ("C:/Windows/Fonts/segoeui.ttf", "C:/Windows/Fonts/arial.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"):
                    try:
                        return ImageFont.truetype(candidate, size)
                    except OSError:
                        pass
                return ImageFont.load_default()

            def ordered_box(p):
                return (min(p[0], p[2]), min(p[1], p[3]), max(p[0], p[2]), max(p[1], p[3]))

            # Translucent highlighting is rendered before text and objects.
            # This prevents a later highlighter stroke from obscuring letters.
            highlight_layer = Image.new("RGBA", (board_w, board_h), (0, 0, 0, 0))
            highlight_draw = ImageDraw.Draw(highlight_layer)
            for h in self.strokes:
                if h.get("shape") != "highlighter" or h.get("id") in erased or h.get("id") in deleted:
                    continue
                hp = h.get("points", [])
                if not isinstance(hp, (tuple, list)) or len(hp) != 4:
                    continue
                hc = h.get("color", "#FFFF00")
                try:
                    from PIL import ImageColor
                    rgb = ImageColor.getrgb(hc)
                    hw = max(1, int(h.get("width", 22)))
                    highlight_draw.line(tuple(hp), fill=(*rgb, 85), width=hw)
                except (ValueError, TypeError):
                    pass
            result = Image.alpha_composite(result.convert("RGBA"), highlight_layer).convert("RGB")
            draw = ImageDraw.Draw(result)

            for stroke in self.strokes:
                shape = stroke.get("shape")
                if shape in ("eraser", "object_edit", "object_delete", "text_edit", "text_delete", "laser", "highlighter"):
                    continue
                sid = stroke.get("id")
                if sid in erased or sid in deleted:
                    continue
                p = object_updates.get(sid, stroke.get("points", [0, 0, 0, 0]))
                if not isinstance(p, (list, tuple)) or len(p) != 4:
                    continue
                x1, y1, x2, y2 = map(float, p)
                color = stroke.get("color", "#4F46E5")
                width = max(1, int(round(float(stroke.get("width", 2)))))
                box = ordered_box((x1, y1, x2, y2))
                if shape in ("pen", "freehand", "marker", "highlighter"):
                    draw.line((x1, y1, x2, y2), fill=color, width=width)
                    radius = width / 2
                    draw.ellipse((x2-radius, y2-radius, x2+radius, y2+radius), fill=color)
                elif shape == "line":
                    draw.line((x1, y1, x2, y2), fill=color, width=width)
                elif shape == "rectangle":
                    draw.rectangle(box, outline=color, width=width)
                elif shape == "oval":
                    draw.ellipse(box, outline=color, width=width)
                elif shape == "circle":
                    side = min(abs(x2-x1), abs(y2-y1))
                    cx = x1 + (side if x2 >= x1 else -side)
                    cy = y1 + (side if y2 >= y1 else -side)
                    draw.ellipse(ordered_box((x1, y1, cx, cy)), outline=color, width=width)
                elif shape == "triangle":
                    pts = [((x1+x2)/2, y1), (x1, y2), (x2, y2)]
                    draw.line(pts + [pts[0]], fill=color, width=width, joint="curve")
                elif shape == "image":
                    try:
                        raw = _base64.b64decode(stroke.get("image", ""))
                        picture = Image.open(_io.BytesIO(raw)).convert("RGBA")
                        iw, ih = max(1, int(abs(x2-x1))), max(1, int(abs(y2-y1)))
                        picture = picture.resize((iw, ih), Image.Resampling.LANCZOS)
                        result.paste(picture, (int(x1), int(y1)), picture)
                    except Exception:
                        pass
                elif shape == "text":
                    edit = text_updates.get(sid)
                    if edit:
                        x1, y1 = edit["points"][:2]
                        width = max(1, int(edit.get("width", width)))
                    draw.multiline_text((x1, y1), stroke.get("text", ""), fill=color,
                                        font=font(max(12, width * 4)), spacing=3)
                elif shape == "sticky_note":
                    draw.rectangle((x1+4, y1+5, x2+4, y2+5), fill="#CBD5E1")
                    draw.rectangle(box, fill=color, outline="#64748B", width=1)
                    note_text = stroke.get("text", "")
                    note_font = font(15)
                    max_text_width = max(30, int(abs(x2-x1))-24)
                    lines = []
                    for paragraph in note_text.split("\n"):
                        current = ""
                        for word in paragraph.split(" "):
                            candidate = (current + " " + word).strip()
                            if current and draw.textbbox((0,0), candidate, font=note_font)[2] > max_text_width:
                                lines.append(current)
                                current = word
                            else:
                                current = candidate
                        lines.append(current)
                    try:
                        text_color = self.color_text(color)
                    except Exception:
                        text_color = "#17243B"
                    draw.multiline_text((x1+12, y1+12), "\n".join(lines), fill=text_color,
                                        font=note_font, spacing=3)

            if file_type == "png":
                result.save(selected, "PNG")
            else:
                result.save(selected, "PDF", resolution=100.0)
            self.toast("Full whiteboard exported: " + selected, "success")
        except Exception as error:
            messagebox.showerror("Export failed", str(error))

    def redraw(self):

        if self.page != "board":
            return

        self.canvas.delete("all")
        self.image_refs = {}
        if self.grid_visible:
            self.draw_grid()
        if self.selected_text and self.text_state(self.selected_text) is None:
            self.selected_text = None
        self.preview = None
        self.cursor_items = {}
        self.below_indicators = {}
        self.local_laser = None

        text_previews = list(self.remote_text_previews.items())
        self.remote_text_previews = {}
        previews = list(
            self.remote_previews.items()
        )
        self.remote_previews = {}

        erased_ids = {
            target
            for event in self.strokes
            if event.get("shape") == "eraser"
            for target in event.get("targets", [])
        }
        deleted = {e.get("target") for e in self.strokes if e.get("shape") == "object_delete"}
        updates = {}
        for e in self.strokes:
            if e.get("shape") == "object_edit":
                updates[e.get("target")] = e.get("points")
        for stroke in self.strokes:
            if stroke.get("shape") in ("eraser", "object_edit", "object_delete") or stroke.get("id") in erased_ids or stroke.get("id") in deleted:
                continue
            rendered = dict(stroke)
            if stroke.get("id") in updates:
                rendered["points"] = updates[stroke["id"]]
            self.expand_for_stroke(rendered)
            self.paint(rendered)

        # Keep note lettering above overlapping drawings and selection borders.
        self.canvas.tag_raise("sticky_note_text")
        self.update_text_selection()
        self.update_object_selection()
        for name, data in text_previews:
            self.show_text_preview({**data, "username": name, "visible": True})

        for name, data in previews:

            self.show_shape_preview({
                **data,
                "username": name,
                "visible": True
            })

        for name, data in list(
            self.remote_cursors.items()
        ):

            self.show_remote_cursor({
                **data,
                "username": name,
                "visible": True
            })

    # ---------- LIVE CURSORS ----------

    def send_cursor(self, event, force=False):

        if self.page != "board":
            return

        if self.tool == "laser":
            x, y = self.canvas_position(event)
            self.show_local_laser(x, y)
        if not self.connected:
            return

        now = time.monotonic()

        if (
            not force
            and now-self.last_cursor_send < .02
        ):
            return

        self.last_cursor_send = now

        x, y = self.canvas_position(event)

        self.send({
            "type": "cursor",
            "x": x,
            "y": y,
            "visible": True,
            "laser": self.tool == "laser"
        })

    def show_local_laser(self, x, y):
        self.hide_local_laser()
        self.local_laser = self.canvas.create_oval(
            x-7, y-7, x+7, y+7,
            fill="#FF1744", outline="white", width=2,
            tags="laser_overlay"
        )
        self.canvas.tag_raise("laser_overlay")

    def hide_local_laser(self):
        if self.local_laser is not None and self.page == "board":
            self.canvas.delete(self.local_laser)
        self.local_laser = None

    def hide_cursor(self, event=None):

        self.hide_local_laser()
        if self.connected:

            self.send({
                "type": "cursor",
                "x": 0,
                "y": 0,
                "visible": False
            })

    def show_remote_cursor(self, msg):

        if self.page != "board":
            return

        name = msg.get("username", "")

        if not name or name == self.username:
            return

        if not msg.get("visible", True):

            self.remove_remote_cursor(name)
            return

        x = msg["x"]
        y = msg["y"]
        color = msg.get("color", BLUE)
        laser = bool(msg.get("laser", False))

        self.expand_whiteboard(y)

        self.remote_cursors[name] = {
            "x": x,
            "y": y,
            "color": color,
            "laser": laser
        }

        for item in self.cursor_items.pop(name, []):
            self.canvas.delete(item)

        if laser:
            glow = self.canvas.create_oval(
                x-13, y-13, x+13, y+13,
                outline="#FF8A9F", width=3,
                tags="remote_cursor"
            )
            dot = self.canvas.create_oval(
                x-7, y-7, x+7, y+7,
                fill="#FF1744", outline="white", width=2,
                tags="remote_cursor"
            )
            label = self.canvas.create_text(
                x+16, y+13, text=name + "  • Laser",
                anchor="nw", fill="#E11D48",
                font=("Segoe UI", 10, "bold"),
                tags="remote_cursor"
            )
            self.cursor_items[name] = [glow, dot, label]
            self.canvas.tag_raise("remote_cursor")
            self.update_below_indicator(name)
            return

        arrow = self.canvas.create_polygon(
            x, y,
            x, y+19,
            x+5, y+15,
            x+10, y+25,
            x+14, y+23,
            x+9, y+13,
            x+18, y+13,
            fill=color,
            outline=WHITE,
            tags="remote_cursor"
        )

        label = self.canvas.create_text(
            x+15, y+31,
            text=name,
            anchor="nw",
            fill=WHITE,
            font=("Segoe UI", 10, "bold"),
            tags="remote_cursor"
        )

        bounds = self.canvas.bbox(label)

        background = self.canvas.create_rectangle(
            bounds[0]-5,
            bounds[1]-3,
            bounds[2]+5,
            bounds[3]+3,
            fill=color,
            outline=color,
            tags="remote_cursor"
        )

        self.canvas.tag_lower(
            background, label
        )

        self.canvas.tag_raise(
            "remote_cursor"
        )

        self.cursor_items[name] = [
            arrow, label, background
        ]
        self.update_below_indicator(name)

    def refresh_below_indicators(self):
        if self.page != "board":
            return
        for name in list(self.remote_cursors):
            self.update_below_indicator(name)

    def update_below_indicator(self, name):
        if self.page != "board":
            return
        for item in self.below_indicators.pop(name, []):
            self.canvas.delete(item)
        data = self.remote_cursors.get(name)
        if not data:
            return
        left = self.canvas.canvasx(0)
        top = self.canvas.canvasy(0)
        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())
        bottom = top + height
        if data["y"] <= bottom + 4:
            return
        x = max(left + 65, min(left + width - 65, data["x"]))
        y = bottom - 43
        color = data.get("color", BLUE)
        arrow = self.canvas.create_polygon(
            x - 10, y, x + 10, y, x, y + 15,
            fill=color, outline=WHITE, width=1,
            tags="below_indicator"
        )
        label = self.canvas.create_text(
            x, y - 4, anchor="s", text=name + " drawing below",
            fill=WHITE, font=("Segoe UI", 9, "bold"),
            tags="below_indicator"
        )
        bbox = self.canvas.bbox(label)
        bg = self.canvas.create_rectangle(
            bbox[0] - 5, bbox[1] - 3,
            bbox[2] + 5, bbox[3] + 3,
            fill=color, outline=color, tags="below_indicator"
        )
        self.canvas.tag_lower(bg, label)
        self.canvas.tag_raise("below_indicator")
        self.below_indicators[name] = [arrow, label, bg]

    def remove_remote_cursor(self, name):
        for item in self.below_indicators.pop(name, []):
            self.canvas.delete(item)

        for item in self.cursor_items.pop(name, []):
            self.canvas.delete(item)

        self.remote_cursors.pop(name, None)

    # ---------- LIVE SHAPE PREVIEWS ----------

    def send_shape_preview(
        self, points, visible=True, force=False
    ):

        if (
            not self.connected
            or self.page != "board"
            or self.tool not in SHAPES
        ):
            return

        now = time.monotonic()

        if (
            visible
            and not force
            and now-self.last_preview_send < .025
        ):
            return

        self.last_preview_send = now

        self.send({
            "type": "shape_preview",
            "shape": self.tool,
            "points": points,
            "color": self.color,
            "width": self.size.get(),
            "visible": visible
        })

    def show_shape_preview(self, msg):

        if self.page != "board":
            return

        name = msg.get("username", "")

        if not name or name == self.username:
            return

        self.clear_shape_preview(name)

        if not msg.get("visible", True):
            return

        if msg.get("shape") not in SHAPES:
            return

        self.expand_whiteboard(
            max(
                msg["points"][1],
                msg["points"][3]
            )
        )

        item = self.draw_shape(
            msg["shape"],
            msg["points"],
            msg["color"],
            msg["width"]
        )

        self.canvas.addtag_withtag(
            "remote_preview",
            item
        )

        self.remote_previews[name] = {
            "item": item,
            "shape": msg["shape"],
            "points": msg["points"],
            "color": msg["color"],
            "width": msg["width"]
        }

        self.canvas.tag_raise(
            "remote_cursor"
        )

    def clear_shape_preview(self, name):

        data = self.remote_previews.pop(
            name, None
        )

        if data and data.get("item") is not None:
            self.canvas.delete(data["item"])

    def clear_remote_overlays(self):

        for name in list(self.remote_cursors):
            self.remove_remote_cursor(name)

        for name in list(self.remote_previews):
            self.clear_shape_preview(name)

    # ---------- CHAT ----------

    def refresh_chat_settings_button(self):
        if self.chat_settings_button and self.chat_settings_button.winfo_exists():
            if self.owner:
                self.chat_settings_button.pack(side="right")
            else:
                self.chat_settings_button.pack_forget()

    def open_chat_settings(self):
        if not self.owner or self.page != "board":
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("Host Chat Settings")
        dialog.geometry("380x490")
        dialog.transient(self.root)
        dialog.grab_set()
        body = tk.Frame(dialog, padx=18, pady=14)
        body.pack(fill="both", expand=True)
        def action(operation, **kwargs):
            self.send({"type":"chat_settings", "operation":operation, **kwargs})
        tk.Label(body, text="Group Chat Settings", font=("Segoe UI", 15, "bold")).pack(pady=6)
        tk.Button(body, text="Unlock Chat" if self.chat_locked else "Lock Chat",
            command=lambda: (action("lock", value=not self.chat_locked), dialog.destroy())).pack(fill="x", pady=5)
        tk.Button(body, text="Clear All Messages", command=lambda: (
            action("clear"), dialog.destroy()) if messagebox.askyesno("Clear Chat", "Delete all chat messages for everyone?", parent=dialog) else None).pack(fill="x", pady=5)
        tk.Label(body, text="Slow Mode (seconds between messages)").pack(pady=(12,3))
        slow = tk.StringVar(value=str(self.chat_slow))
        ttk.Combobox(body, textvariable=slow, values=["0","5","10","30","60"], state="readonly").pack(fill="x")
        tk.Button(body, text="Apply Slow Mode", command=lambda: action("slow", seconds=int(slow.get()))).pack(fill="x", pady=5)
        tk.Label(body, text="Mute / Unmute Participant").pack(pady=(12,3))
        names = [n for n in self.participants if n != self.meeting_owner]
        chosen = tk.StringVar(value=names[0] if names else "")
        ttk.Combobox(body, textvariable=chosen, values=names, state="readonly").pack(fill="x")
        tk.Button(body, text="Mute", command=lambda: action("mute", username=chosen.get(), value=True)).pack(fill="x", pady=3)
        tk.Button(body, text="Unmute", command=lambda: action("mute", username=chosen.get(), value=False)).pack(fill="x", pady=3)
        tk.Label(body, text="Delete individual message").pack(pady=(12,3))
        entries = [e for e in self.chat_history if not e.get("system") and e.get("id")]
        labels = [f"{e.get('user','')}: {e.get('text','')[:35]}" for e in entries]
        selected = tk.StringVar(value=labels[-1] if labels else "")
        ttk.Combobox(body, textvariable=selected, values=labels, state="readonly").pack(fill="x")
        def delete_selected():
            if selected.get() in labels:
                action("delete", id=entries[labels.index(selected.get())]["id"])
                dialog.destroy()
        tk.Button(body, text="Delete Selected Message", command=delete_selected).pack(fill="x", pady=5)

    def redraw_chat(self):

        if self.page != "board":
            return

        self.chat.configure(state="normal")
        self.chat.delete("1.0", "end")

        for entry in self.chat_history:
            if entry.get("system"):
                self.chat.insert("end", entry.get("text", "") + "\n", "system")
                continue
            name = entry.get("user", "")
            tag = "user_" + re.sub(r"[^a-zA-Z0-9_]", "_", name)
            self.chat.tag_configure(tag, foreground=self.participant_colors.get(name, "#93C5FD"))
            self.chat.insert("end", f"[{entry.get('time', '')}] ")
            self.chat.insert("end", name, tag)
            self.chat.insert("end", f": {entry.get('text', '')}\n")
        self.chat.tag_configure("system", foreground="#FBBF24")

        self.chat.see("end")
        self.chat.configure(state="disabled")

    def send_chat(self):

        text = self.message.get().strip()

        if not text:
            return

        entry = {
            "type": "chat",
            "id": uuid.uuid4().hex,
            "user": self.username,
            "text": text[:500],
            "time": datetime.now().strftime("%H:%M")
        }

        if not self.owner and (self.chat_locked or self.username in self.chat_muted):
            self.toast("Chat locked" if self.chat_locked else "You are muted", "warning")
            return
        self.chat_history.append(entry)
        self.redraw_chat()
        self.message.delete(0, "end")
        self.queue_event(entry)

    # ---------- MEETING CONTROLS ----------

    def remove_participant(self):

        selected = self.users.curselection()

        if not selected or not self.connected:
            return

        name = self.participants[selected[0]]

        if name in (
            self.username,
            self.meeting_owner
        ):

            messagebox.showerror(
                "Error",
                "Cannot remove yourself or meeting owner"
            )
            return

        if messagebox.askyesno(
            "Remove Participant",
            f"Remove {name}?"
        ):

            self.send({
                "type": "remove_user",
                "username": name
            })

    def send_action(self, action):

        if self.connected:
            self.send({"type": action})

    def update_lock_button(self):
        button = getattr(self, "lock_button", None)
        if button is None or self.page != "board":
            return
        try:
            button.configure(
                text="Unlock" if self.locked else "Lock",
                bg="#DC2626" if self.locked else "#16A34A",
                activebackground="#B91C1C" if self.locked else "#15803D",
                fg="white", activeforeground="white"
            )
        except tk.TclError:
            pass

    def toggle_lock(self):

        if self.connected and self.owner:

            self.send({
                "type": "lock",
                "locked": not self.locked
            })

    def end_meeting(self):

        if self.connected and self.owner:

            if messagebox.askyesno(
                "End Meeting",
                "End meeting for everyone?"
            ):

                self.send({
                    "type": "end_meeting"
                })

    def update_buttons(self):

        if self.page != "board":
            return

        for button in self.online_buttons:

            button.configure(
                state=(
                    "normal" if self.connected
                    else "disabled"
                )
            )

        for button in self.owner_buttons:

            button.configure(
                state=(
                    "normal"
                    if self.connected and self.owner
                    else "disabled"
                )
            )


        for widget in self.meeting_buttons.winfo_children():
            widget.destroy()

        if self.owner:

            ttk.Button(
                self.meeting_buttons,
                text="End Meeting",
                style="Danger.TButton",
                command=self.end_meeting
            ).pack(fill="x", pady=4)

        ttk.Button(
            self.meeting_buttons,
            text="Leave Meeting",
            style="Dark.TButton",
            command=self.close
        ).pack(fill="x", pady=4)

        self.status.configure(
            text=(
                "● Connected"
                if self.connected
                else "● Reconnecting..."
            ),
            foreground=(
                GREEN if self.connected
                else BLUE
            )
        )

        self.pending_label.configure(text=f"Pending: {len(self.pending)}")
        self.update_connection_pill()

    # ---------- LOCAL STORAGE ----------

    def local_path(self):

        os.makedirs(
            "client_data",
            exist_ok=True
        )

        name = re.sub(
            r"[^A-Za-z0-9_]",
            "_",
            self.username + "_" + self.room
        )

        return os.path.join(
            "client_data",
            name + ".json"
        )

    def save_local(self):

        if not self.room:
            return

        path = self.local_path()

        with open(
            path + ".tmp",
            "w",
            encoding="utf-8"
        ) as f:

            json.dump({
                "strokes": self.strokes,
                "chat": self.chat_history,
                "pending": self.pending
            }, f)

        os.replace(
            path + ".tmp",
            path
        )

    def load_local(self):

        try:

            with open(
                self.local_path(),
                encoding="utf-8"
            ) as f:

                data = json.load(f)

            self.strokes = data.get(
                "strokes", []
            )

            self.chat_history = data.get(
                "chat", []
            )

            self.pending = data.get(
                "pending", []
            )

        except (OSError, ValueError):

            self.strokes = []
            self.chat_history = []
            self.pending = []

    def retry_pending_sync(self):
        if self.closing:
            return
        if (self.page == "board" and self.connected and
                self.recovery_sync_ready and self.pending):
            for event in list(self.pending):
                if event.get("type") in ("stroke", "chat"):
                    self.send(event)
        try:
            self.root.after(1200, self.retry_pending_sync)
        except (RuntimeError, tk.TclError):
            pass

    def queue_event(self, event):

        self.pending.append(event)
        self.save_local()

        if self.connected:
            self.send(event)

        self.update_buttons()

    # ---------- NETWORK ----------

    def send(self, data):

        sock = self.sock

        if sock is None:
            return False

        try:

            with self.send_lock:

                sock.sendall(
                    (json.dumps(data) + "\n").encode()
                )

            return True

        except OSError:

            self.disconnected(sock)
            return False

    def receive(self, sock):

        try:

            with sock.makefile(
                "r",
                encoding="utf-8"
            ) as stream:

                for line in stream:

                    msg = json.loads(line)

                    self.root.after(
                        0,
                        self.handle,
                        msg,
                        sock
                    )

        except (
            OSError,
            ValueError,
            UnicodeError,
            RuntimeError
        ):
            pass

        try:

            self.root.after(
                0,
                self.disconnected,
                sock
            )

        except RuntimeError:
            pass

    def disconnected(self, sock):

        if self.closing or sock != self.sock:
            return

        self.sock = None
        self.connected = False
        self.recovery_sync_ready = False

        try:
            sock.close()
        except OSError:
            pass

        if self.page in ("ended", "removed"):
            return

        if self.page == "board":

            self.save_local()
            self.clear_remote_overlays()
            self.update_buttons()
            self.start_reconnect()

        else:

            messagebox.showwarning(
                "Disconnected",
                "Server disconnected"
            )

            self.build_login()

    def start_reconnect(self):

        if self.closing or self.page != "board":
            return

        self.reconnecting = True

        self.root.after(
            2000,
            self.try_reconnect
        )

    def try_reconnect(self):

        if (
            self.closing
            or self.page != "board"
            or self.sock is not None
            or self.reconnect_busy
        ):
            return

        self.reconnect_busy = True

        def worker():

            try:

                sock = socket.create_connection(
                    (self.server_ip, self.server_port),
                    timeout=2
                )

                sock.settimeout(None)

                self.root.after(
                    0,
                    self.reconnect_ready,
                    sock
                )

            except OSError:

                try:
                    self.root.after(
                        2000,
                        self.try_reconnect
                    )
                except RuntimeError:
                    pass

            finally:
                self.reconnect_busy = False

        threading.Thread(
            target=worker,
            daemon=True
        ).start()

    def reconnect_ready(self, sock):

        if (
            self.closing
            or self.page != "board"
            or self.sock is not None
        ):

            sock.close()
            return

        self.sock = sock
        self.recovery_sync_ready = False
        self.recovery_resync_needed = True

        threading.Thread(
            target=self.receive,
            args=(sock,),
            daemon=True
        ).start()

        self.send({
            "type": "login",
            "username": self.username,
            "password": self.password,
            "role": self.role
        })

    def merge_state(self, msg):

        server_strokes = msg.get(
            "strokes", []
        )

        server_chat = msg.get(
            "chat", []
        )

        stroke_ids = {
            s.get("id")
            for s in server_strokes
        }

        chat_ids = {
            c.get("id")
            for c in server_chat
        }

        self.pending = [
            e for e in self.pending
            if e.get("id") not in (
                stroke_ids
                if e.get("type") == "stroke"
                else chat_ids
            )
        ]

        self.strokes = server_strokes + [
            e for e in self.pending
            if e.get("type") == "stroke"
        ]

        self.chat_history = server_chat + [
            e for e in self.pending
            if e.get("type") == "chat"
        ]

        self.chat_locked = msg.get("chat_locked", False)
        self.chat_muted = msg.get("chat_muted", [])
        self.chat_slow = msg.get("chat_slow", 0)
        self.locked = msg.get(
            "locked", False
        )
        self.update_lock_button()

        self.meeting_owner = msg.get(
            "owner", ""
        )

        self.owner = (
            self.meeting_owner == self.username
        )

        for stroke in self.strokes:
            self.expand_for_stroke(stroke)

        self.redraw()
        self.redraw_chat()
        self.save_local()

        self.recovery_sync_ready = True
        for event in list(self.pending):
            if event.get("type") in ("stroke", "chat"):
                self.send(event)
        if not self.pending and self.recovery_resync_needed:
            self.recovery_resync_needed = False
            self.send({"type": "sync_request"})

        self.update_buttons()
        self.refresh_chat_settings_button()

    def show_notice(self, title, message):

        self.page = title.lower()
        self.connected = False
        self.reconnecting = False

        self.clear_page()

        outer = tk.Frame(
            self.root,
            bg=BG
        )
        outer.pack(expand=True)

        card = self.card(
            outer, 450, 250
        )

        tk.Label(
            card,
            text=message,
            font=("Segoe UI", 17, "bold"),
            fg=NAVY,
            bg=WHITE,
            wraplength=300
        ).pack(pady=(20, 25))

        RoundedButton(
            card,
            "Close",
            self.close
        ).pack()

    # ---------- SERVER MESSAGES ----------

    def handle(self, msg, sock):

        if self.closing or sock != self.sock:
            return

        kind = msg.get("type")

        if kind == "owner_transfer_success":
            if getattr(self, "pending_owner_exit", False):
                self.pending_owner_exit = False
                self.save_local()
                self.finish_close()
            return

        elif kind == "owner_changed":
            self.meeting_owner = msg.get("owner", "")
            self.owner = self.meeting_owner == self.username
            if self.page == "board":
                self.toast(f"{self.meeting_owner} is now the meeting owner", "info")
                self.update_buttons()
                self.refresh_chat_settings_button()
            return

        elif kind == "generated_room_id":
            if self.page == "room_form" and hasattr(self, "room_id_field"):
                self.room_id_field.set(msg.get("room", ""))

        elif kind == "login_success":

            if self.reconnecting:

                self.send({
                    "type": "join",
                    "room": self.room,
                    "password": self.room_password
                })

            else:
                self.build_dashboard()

        elif kind == "joined":

            self.room = msg["room"]
            self.owner = msg["owner"]

            if self.reconnecting:

                self.reconnecting = False
                self.connected = True
                self.update_buttons()

            else:

                self.load_local()
                self.connected = True
                self.board_height = 3000
                self.build_board()

        elif kind == "state" and self.page == "board":

            self.merge_state(msg)

        elif kind == "stroke" and self.page == "board":

            stroke = msg["stroke"]

            self.clear_shape_preview(
                stroke.get("user", "")
            )
            self.clear_text_preview(stroke.get("user", ""))

            if stroke.get("id") not in {
                s.get("id")
                for s in self.strokes
            }:

                self.strokes.append(stroke)
                self.expand_for_stroke(stroke)
                self.paint(stroke)
                if stroke.get("shape") in ("object_edit", "object_delete"):
                    self.redraw()
                if stroke.get("shape") in ("text_edit", "text_delete"):
                    if stroke.get("shape") == "text_delete" and stroke.get("target") == self.selected_text:
                        self.selected_text = None
                    self.update_text_selection()
                self.save_local()

        elif kind == "chat_settings_state" and self.page == "board":
            self.chat_locked = bool(msg.get("locked", False))
            self.chat_muted = msg.get("muted", [])
            self.chat_slow = msg.get("slow", 0)
            self.toast("Chat settings updated", "info")

        elif kind == "chat_cleared" and self.page == "board":
            self.chat_history = []
            self.pending = [e for e in self.pending if e.get("type") != "chat"]
            self.redraw_chat()
            self.save_local()

        elif kind == "chat_deleted" and self.page == "board":
            self.chat_history = [e for e in self.chat_history if e.get("id") != msg.get("id")]
            self.pending = [e for e in self.pending if e.get("id") != msg.get("id")]
            self.redraw_chat()
            self.save_local()

        elif kind == "chat" and self.page == "board":

            entry = msg["entry"]

            if entry.get("id") not in {
                c.get("id")
                for c in self.chat_history
            }:

                self.chat_history.append(entry)
                if self.chat_collapsed:
                    self.unread += 1
                    self.refresh_chat_toggle()
                self.redraw_chat()
                self.save_local()

        elif kind == "cursor" and self.page == "board":

            self.show_remote_cursor(msg)

        elif kind == "shape_preview" and self.page == "board":

            self.show_shape_preview(msg)

        elif kind == "text_preview" and self.page == "board":
            self.show_text_preview(msg)

        elif kind == "cursor_leave" and self.page == "board":

            name = msg.get(
                "username", ""
            )

            self.remove_remote_cursor(name)
            self.clear_shape_preview(name)
            self.clear_text_preview(name)

        elif kind == "clear_previews" and self.page == "board":

            for name in list(self.remote_previews):
                self.clear_shape_preview(name)
            for name in list(self.remote_text_previews):
                self.clear_text_preview(name)

        elif kind == "ack":

            self.pending = [
                e for e in self.pending
                if e.get("id") != msg["id"]
            ]

            self.save_local()
            self.update_buttons()
            if (self.recovery_sync_ready and not self.pending and
                    self.recovery_resync_needed):
                self.recovery_resync_needed = False
                self.send({"type": "sync_request"})

        elif kind == "rejected":

            self.pending = [
                e for e in self.pending
                if e.get("id") != msg["id"]
            ]

            if self.page == "board":

                self.strokes = [
                    s for s in self.strokes
                    if s.get("id") != msg["id"]
                ]

                self.redraw()
                self.chat_history = [e for e in self.chat_history if e.get("id") != msg.get("id")]
                self.redraw_chat()

            self.save_local()

            self.toast(msg.get("message", "Event rejected"), "error")

        elif kind == "hand_raised" and self.page == "board":
            name = msg.get("username", "Student")
            if msg.get("raised", True):
                self.raised_hands.add(name)
                self.show_notification(name, "raised hand")
            else:
                self.raised_hands.discard(name)
            self.update_hand_button()

        elif kind == "snapshot_list" and self.page == "board":
            self.show_snapshots(msg.get("snapshots", []))

        elif kind == "users" and self.page == "board":

            # Detect joins and leaves and show notifications
            self.update_participants(msg)

        elif kind == "locked":

            self.locked = msg["locked"]
            self.update_lock_button()
            if self.page == "board":
                self.toast("Board locked" if self.locked else "Board unlocked", "info")

            if self.locked and self.role != "host" and not self.owner and self.page == "board":

                if self.preview is not None:

                    self.canvas.delete(self.preview)
                    self.preview = None

                self.start_point = None

        elif kind == "meeting_ended":

            self.show_notice(
                "Ended",
                "Host ended the meeting"
            )

        elif kind == "removed":

            self.pending = []

            self.show_notice(
                "Removed",
                msg.get(
                    "message",
                    "Removed from meeting"
                )
            )

        elif kind == "error":

            if (
                self.reconnecting
                and self.page == "board"
            ):

                self.show_notice(
                    "Ended",
                    "Unable to rejoin the meeting"
                )

            else:

                self.toast(msg.get("message", "Unknown error"), "error")

        elif kind == "info":
            self.toast(msg.get("message", "Saved"), "success")

        elif kind == "pong":
            nonce = msg.get("nonce")
            sent = self.ping_sent.pop(nonce, None)
            if sent is not None:
                self.last_ping = round((time.monotonic() - sent) * 1000)
                self.update_connection_pill()

    # ---------- CLOSE ----------

    def choose_new_owner(self):
        candidates = [name for name in self.participants if name != self.username]
        if not candidates:
            return None
        dialog = tk.Toplevel(self.root)
        dialog.title("Transfer Meeting Ownership")
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.resizable(False, False)
        tk.Label(dialog, text="Choose the new meeting owner before leaving:",
                 padx=18, pady=12).pack()
        choice = tk.StringVar(value=candidates[0])
        selector = ttk.Combobox(dialog, textvariable=choice, values=candidates,
                                state="readonly", width=28)
        selector.pack(padx=18, pady=8)
        result = {"name": None}
        def confirm():
            if choice.get() in candidates:
                result["name"] = choice.get()
                dialog.destroy()
        controls = tk.Frame(dialog)
        controls.pack(pady=12)
        ttk.Button(controls, text="Transfer and Leave", command=confirm).pack(side="left", padx=6)
        ttk.Button(controls, text="Cancel", command=dialog.destroy).pack(side="left", padx=6)
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        self.root.wait_window(dialog)
        return result["name"]

    def close(self):
        if self.closing:
            return
        if self.page == "board":
            if self.owner:
                others = [n for n in self.participants if n != self.username]
                if not others:
                    if not messagebox.askyesno("End Meeting",
                            "You are the only participant. Leaving will end the meeting. Continue?",
                            parent=self.root):
                        return
                    if not self.connected:
                        messagebox.showwarning("Offline", "Reconnect before ending the meeting.", parent=self.root)
                        return
                    self.send({"type": "end_meeting"})
                else:
                    choice = messagebox.askyesnocancel(
                        "Exit Meeting",
                        "End the meeting for everyone?\n\nYes = End meeting\nNo = Transfer ownership and leave\nCancel = Stay",
                        parent=self.root)
                    if choice is None:
                        return
                    if not self.connected:
                        messagebox.showwarning("Offline", "Reconnect before leaving as owner.", parent=self.root)
                        return
                    if choice:
                        self.send({"type": "end_meeting"})
                    else:
                        target = self.choose_new_owner()
                        if not target:
                            return
                        self.send({"type": "transfer_owner", "username": target})
                        # Wait for server confirmation before disconnecting.
                        self.pending_owner_exit = True
                        return
            else:
                if not messagebox.askyesno("Leave Meeting",
                        "Do you want to leave the meeting?", parent=self.root):
                    return
            self.save_local()
        self.finish_close()

    def finish_close(self):
        if self.closing:
            return
        self.reset_notifications()
        self.closing = True
        if self.sock:
            if self.connected:
                self.send({"type": "exit"})
            try:
                self.sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            try:
                self.sock.close()
            except OSError:
                pass
            self.sock = None
        self.root.destroy()


if __name__ == "__main__":
    Whiteboard()
