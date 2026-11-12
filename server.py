import socket, threading, json, os, hashlib, secrets, re, math, base64, uuid, copy
from datetime import datetime

HOST, PORT = "0.0.0.0", 5000
LIMIT = 1000000
os.makedirs("cn_data", exist_ok=True)

lock = threading.RLock()
rooms = {}
clients = {}

def load(name, default):
    try:
        with open("cn_data/" + name, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default

def save(name, value):
    path = "cn_data/" + name
    with open(path + ".tmp", "w", encoding="utf-8") as f:
        json.dump(value, f)
    os.replace(path + ".tmp", path)

def password_hash(password, salt):
    return hashlib.pbkdf2_hmac(
        "sha256", password.encode(), bytes.fromhex(salt), 200000
    ).hex()

def account(password, role):
    salt = secrets.token_hex(16)
    return {"salt": salt, "hash": password_hash(password, salt), "role": role}

accounts = load("accounts.json", None)
if accounts is None:
    accounts = {}
    for i in range(1, 4):
        accounts[f"host{i}"] = account(f"host@{i}", "host")
    for i in range(1, 11):
        accounts[f"stud{i}"] = account(f"stud@{i}", "student")
    save("accounts.json", accounts)

for filename in os.listdir("cn_data"):
    if filename.startswith("room_") and filename.endswith(".json"):
        code = filename[5:-5]
        room = load(filename, None)
        if isinstance(room, dict) and not room.get("ended"):
            room.setdefault("strokes", [])
            room.setdefault("chat", [])
            room.setdefault("ids", [])
            room.setdefault("banned", [])
            room.setdefault("locked", False)
            room.setdefault("snapshots", [])
            room["raised_hands"] = set()
            room.update(users={}, redo=[], cursors={}, previews={})
            rooms[code] = room

def send(sock, message):
    try:
        with clients[sock]["lock"]:
            sock.sendall((json.dumps(message) + "\n").encode())
        return True
    except (OSError, KeyError):
        return False

def broadcast(room, message, exclude=None):
    for sock in list(room["users"]):
        if sock != exclude:
            send(sock, message)

def save_room(code):
    room = rooms[code]
    save("room_" + code + ".json", {
        k: v for k, v in room.items()
        if k not in ("users", "redo", "cursors", "previews", "raised_hands")
    })

def state(room):
    return {
        "type": "state",
        "strokes": room["strokes"],
        "chat": room["chat"],
        "locked": room["locked"],
        "owner": room["owner"]
    }

def color_for(name):
    colors = [
        "#e11d48", "#2563eb", "#16a34a", "#9333ea",
        "#ea580c", "#0891b2", "#be185d", "#65a30d"
    ]
    number = int(hashlib.sha256(name.encode()).hexdigest(), 16)
    return colors[number % len(colors)]

def update_users(room):
    broadcast(room, {
        "type": "users",
        "owner": room["owner"],
        "users": [
            {
                "name": name,
                "role": accounts[name]["role"],
                "color": color_for(name),
                "hand_raised": name in room.setdefault("raised_hands", set())
            }
            for name in room["users"].values()
        ]
    })

def remove(sock, code):
    if code not in rooms:
        return
    room = rooms[code]
    name = room["users"].pop(sock, None)
    if name:
        room.setdefault("raised_hands", set()).discard(name)
    if not name:
        return
    room["cursors"].pop(name, None)
    room["previews"].pop(name, None)
    broadcast(room, {"type": "cursor_leave", "username": name})
    if room["owner"] not in room["users"].values():
        hosts = [
            n for n in room["users"].values()
            if accounts[n]["role"] == "host"
        ]
        if hosts:
            room["owner"] = hosts[0]
            save_room(code)
    update_users(room)

def valid_points(points):
    return (
        isinstance(points, list)
        and len(points) == 4
        and all(
            type(v) in (int, float)
            and math.isfinite(v)
            and 0 <= v <= LIMIT
            for v in points
        )
    )

def valid_style(color, width):
    return (
        isinstance(color, str)
        and re.fullmatch(r"#[0-9a-fA-F]{6}", color) is not None
        and type(width) in (int, float)
        and math.isfinite(width)
        and 1 <= width <= 50
    )

def handle(sock, address):
    username = role = code = None
    clients[sock] = {"lock": threading.Lock()}

    try:
        with sock.makefile("r", encoding="utf-8") as stream:
            for line in stream:
                try:
                    msg = json.loads(line)
                    if not isinstance(msg, dict):
                        continue
                    action = msg.get("type")

                    with lock:
                        if action == "ping":
                            send(sock, {"type": "pong", "nonce": msg.get("nonce")})
                            continue

                        if action == "login":
                            if username:
                                continue
                            name = str(msg.get("username", "")).strip()
                            selected = msg.get("role")
                            acc = accounts.get(name)
                            if not acc or acc["role"] != selected:
                                send(sock, {"type": "error", "message": "Invalid login"})
                                continue
                            if not secrets.compare_digest(
                                acc["hash"],
                                password_hash(str(msg.get("password", "")), acc["salt"])
                            ):
                                send(sock, {"type": "error", "message": "Wrong password"})
                                continue
                            username, role = name, selected
                            send(sock, {
                                "type": "login_success",
                                "username": username, "role": role
                            })
                            continue

                        if not username:
                            send(sock, {"type": "error", "message": "Login required"})
                            continue

                        if action == "add_user":
                            if role != "host":
                                continue
                            name = str(msg.get("username", "")).strip()
                            password = str(msg.get("password", ""))
                            new_role = msg.get("role")
                            if (
                                not re.fullmatch(r"[A-Za-z0-9_]{3,24}", name)
                                or len(password) < 4
                                or new_role not in ("host", "student")
                                or name in accounts
                            ):
                                send(sock, {"type": "error", "message": "Invalid or existing account"})
                            else:
                                accounts[name] = account(password, new_role)
                                save("accounts.json", accounts)
                                send(sock, {"type": "info", "message": "User created"})
                            continue

                        if action == "generate_room_id":
                            if role != "host" or code:
                                send(sock, {"type": "error", "message": "Only hosts can generate room IDs"})
                                continue
                            alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
                            for _ in range(100):
                                new_id = "".join(secrets.choice(alphabet) for _ in range(8))
                                if new_id not in rooms and not os.path.exists(
                                    os.path.join("cn_data", "room_" + new_id + ".json")
                                ):
                                    send(sock, {"type": "generated_room_id", "room": new_id})
                                    break
                            else:
                                send(sock, {"type": "error", "message": "Unable to generate a unique room ID"})
                            continue

                        if action in ("create", "join"):
                            if code:
                                continue
                            room_id = str(msg.get("room", "")).upper().strip()
                            password = str(msg.get("password", ""))
                            if not re.fullmatch(r"[A-Z0-9]{3,12}", room_id) or not password:
                                send(sock, {"type": "error", "message": "Invalid room details"})
                                continue

                            if action == "create":
                                if role != "host":
                                    send(sock, {"type": "error", "message": "Only hosts can create rooms"})
                                    continue
                                old_room = load("room_" + room_id + ".json", None)
                                if room_id in rooms or (isinstance(old_room, dict) and not old_room.get("ended", False)):
                                    send(sock, {"type": "error", "message": "Room already exists. Try joining instead."})
                                    continue
                                rooms[room_id] = {
                                    "password": password, "owner": username,
                                    "strokes": [], "chat": [], "ids": [],
                                    "banned": [], "locked": False, "ended": False,
                                    "users": {}, "redo": [], "cursors": {},
                                    "previews": {}, "snapshots": [], "raised_hands": set()
                                }
                                save_room(room_id)
                            else:
                                if room_id not in rooms:
                                    send(sock, {"type": "error", "message": "Room not found"})
                                    continue
                                if username in rooms[room_id]["banned"]:
                                    send(sock, {"type": "removed", "message": "Removed from room"})
                                    continue
                                if rooms[room_id]["password"] != password:
                                    send(sock, {"type": "error", "message": "Wrong room password"})
                                    continue

                            room = rooms[room_id]
                            if username in room["users"].values():
                                send(sock, {"type": "error", "message": "User already connected"})
                                continue

                            code = room_id
                            room["users"][sock] = username
                            send(sock, {
                                "type": "joined", "room": code,
                                "owner": room["owner"] == username
                            })
                            send(sock, state(room))
                            update_users(room)

                            for name, position in room["cursors"].items():
                                if name != username:
                                    send(sock, {
                                        "type": "cursor", "username": name,
                                        "color": color_for(name),
                                        "visible": True, **position
                                    })
                            for name, preview in room["previews"].items():
                                if name != username:
                                    send(sock, preview)
                            continue

                        if action == "exit":
                            break

                        if code not in rooms:
                            continue
                        room = rooms[code]
                        if sock not in room["users"]:
                            break

                        if action == "raise_hand":
                            raised = room.setdefault("raised_hands", set())
                            if username in raised:
                                raised.remove(username)
                                active = False
                            else:
                                raised.add(username)
                                active = True
                            broadcast(room, {"type":"hand_raised", "username":username,
                                             "raised":active})
                            update_users(room)
                            continue

                        if action == "snapshot_list":
                            if room["owner"] == username:
                                send(sock, {"type":"snapshot_list", "snapshots":[
                                    {"id":v["id"],"label":v["label"]}
                                    for v in room.setdefault("snapshots", [])]})
                            continue

                        if action == "snapshot_save" and room["owner"] == username:
                            history = room.setdefault("snapshots", [])
                            history.append({"id":uuid.uuid4().hex,
                                "label":str(msg.get("label","Snapshot"))[:70],
                                "strokes":copy.deepcopy(room["strokes"])})
                            room["snapshots"] = history[-15:]
                            save_room(code)
                            send(sock,{"type":"info","message":"Snapshot saved"})
                            continue

                        if action == "snapshot_restore" and room["owner"] == username:
                            version = next((v for v in room.setdefault("snapshots", [])
                                if v["id"] == msg.get("id")),None)
                            if version:
                                room["strokes"] = copy.deepcopy(version["strokes"])
                                room["redo"].clear()
                                room["ids"] = list(set(room["ids"]) | {e["id"] for e in room["strokes"]})
                                save_room(code)
                                broadcast(room,state(room))
                            continue

                        if action == "cursor":
                            x, y = msg.get("x", 0), msg.get("y", 0)
                            if not valid_points([x, y, x, y]):
                                continue
                            visible = bool(msg.get("visible", True))
                            if visible:
                                room["cursors"][username] = {"x": x, "y": y, "laser": bool(msg.get("laser", False))}
                            else:
                                room["cursors"].pop(username, None)
                            broadcast(room, {
                                "type": "cursor", "username": username,
                                "x": x, "y": y, "visible": visible,
                                "color": color_for(username),
                                "laser": bool(msg.get("laser", False))
                            }, sock)
                            continue

                        if action == "text_preview":
                            target = str(msg.get("target", ""))[:100]
                            visible = bool(msg.get("visible", True))
                            if visible:
                                x, y, width = msg.get("x"), msg.get("y"), msg.get("width")
                                base = next((e for e in room["strokes"]
                                    if e.get("id") == target and e.get("shape") == "text"
                                    and e.get("user") == username), None)
                                if ((room["locked"] and role != "host") or base is None or
                                        not valid_points([x, y, x, y]) or
                                        type(width) is not int or not 1 <= width <= 50):
                                    continue
                            else:
                                x, y, width = 0, 0, 1
                            packet = {"type": "text_preview", "username": username,
                                      "target": target, "x": x, "y": y,
                                      "width": width, "visible": visible}
                            if visible:
                                room["previews"][username] = packet
                            else:
                                room["previews"].pop(username, None)
                            broadcast(room, packet, sock)
                            continue

                        if action == "shape_preview":
                            shape = msg.get("shape")
                            points = msg.get("points")
                            color = msg.get("color")
                            width = msg.get("width")
                            visible = bool(msg.get("visible", True))
                            if (
                                shape not in ("line", "rectangle", "oval", "circle", "triangle")
                                or not valid_points(points)
                                or not valid_style(color, width)
                            ):
                                continue
                            if visible and room["locked"] and role != "host":
                                continue
                            packet = {
                                "type": "shape_preview", "username": username,
                                "shape": shape, "points": points,
                                "color": color, "width": width, "visible": visible
                            }
                            if visible:
                                room["previews"][username] = packet
                            else:
                                room["previews"].pop(username, None)
                            broadcast(room, packet, sock)
                            continue

                        if action in ("stroke", "chat"):
                            event_id = str(msg.get("id", ""))[:100]
                            if not event_id:
                                continue
                            if event_id in room["ids"]:
                                send(sock, {"type": "ack", "id": event_id})
                                continue

                            if action == "stroke":
                                if room["locked"] and role != "host":
                                    send(sock, {
                                        "type": "rejected", "id": event_id,
                                        "message": "Board locked"
                                    })
                                    continue
                                shape = msg.get("shape")
                                points = msg.get("points")
                                color = msg.get("color")
                                width = msg.get("width")
                                if (
                                    shape not in (
                                        "pen", "freehand", "marker", "highlighter",
                                        "eraser", "line", "rectangle", "oval",
                                        "circle", "triangle", "text", "text_edit", "text_delete", "sticky_note", "image", "object_edit", "object_delete"
                                    )
                                    or not valid_points(points)
                                    or not valid_style(color, width)
                                ):
                                    send(sock, {
                                        "type": "rejected", "id": event_id,
                                        "message": "Invalid drawing"
                                    })
                                    continue
                                entry = {
                                    "id": event_id, "user": username,
                                    "shape": shape, "points": points,
                                    "color": color, "width": width
                                }
                                if shape == "image":
                                    data = msg.get("image", "")
                                    if not isinstance(data,str) or len(data) > 1300000:
                                        send(sock,{"type":"rejected","id":event_id,"message":"Image too large"})
                                        continue
                                    try:
                                        raw = base64.b64decode(data,validate=True)
                                        if len(raw)>975000 or not raw.startswith(b"\xff\xd8\xff"):
                                            raise ValueError("Invalid JPEG")
                                    except (ValueError,base64.binascii.Error):
                                        send(sock,{"type":"rejected","id":event_id,"message":"Invalid image"})
                                        continue
                                    entry["image"] = data
                                if shape in ("object_edit", "object_delete"):
                                    target = str(msg.get("target", ""))[:100]
                                    prior = next((e for e in room["strokes"] if e.get("id") == target
                                        and e.get("shape") in ("image","sticky_note","line","rectangle","oval","circle","triangle")),None)
                                    if prior is None or (role != "host" and prior["user"] != username):
                                        send(sock,{"type":"rejected","id":event_id,"message":"Cannot modify another user's object"})
                                        continue
                                    if any(e.get("shape")=="object_delete" and e.get("target")==target for e in room["strokes"]):
                                        send(sock,{"type":"rejected","id":event_id,"message":"Object already deleted"})
                                        continue
                                    entry["target"] = target
                                if shape in ("text", "sticky_note"):
                                    entry["text"] = str(msg.get("text", ""))[:500]
                                if shape == "sticky_note":
                                    # Keep note dimensions bounded and reject empty notes.
                                    if (not entry["text"].strip()
                                            or points[2] <= points[0]
                                            or points[3] <= points[1]
                                            or points[2] - points[0] > 600
                                            or points[3] - points[1] > 500):
                                        send(sock, {"type": "rejected", "id": event_id,
                                                    "message": "Invalid sticky note"})
                                        continue
                                if shape in ("pen", "freehand", "marker", "highlighter", "eraser"):
                                    group = msg.get("group")
                                    if isinstance(group, str) and 1 <= len(group) <= 100:
                                        entry["group"] = group
                                if shape in ("text_edit", "text_delete"):
                                    target = str(msg.get("target", ""))[:100]
                                    base = next((e for e in room["strokes"]
                                        if e.get("id") == target and
                                        e.get("shape") == "text" and
                                        e.get("user") == username), None)
                                    if base is None or any(
                                        e.get("shape") == "text_delete" and e.get("target") == target
                                        for e in room["strokes"]
                                    ):
                                        send(sock, {"type": "rejected", "id": event_id,
                                                    "message": "Text not found, already deleted, or not owned by you"})
                                        continue
                                    entry["target"] = target
                                    entry["color"] = base["color"]
                                if shape == "eraser":
                                    # An eraser removes only permitted drawing objects.
                                    # Students may erase their own; hosts may erase anyone's.
                                    ax, ay, bx, by = points
                                    margin = width / 2 + 3
                                    left, right = min(ax, bx)-margin, max(ax, bx)+margin
                                    top, bottom = min(ay, by)-margin, max(ay, by)+margin
                                    already_erased = {
                                        target
                                        for prior in room["strokes"]
                                        if prior.get("shape") == "eraser"
                                        for target in prior.get("targets", [])
                                    }
                                    targets = []
                                    for prior in room["strokes"]:
                                        if prior.get("id") in already_erased:
                                            continue
                                        if prior.get("shape") in ("eraser", "text_edit", "text_delete"):
                                            continue
                                        if role != "host" and prior.get("user") != username:
                                            continue
                                        px1, py1, px2, py2 = prior["points"]
                                        pad = prior.get("width", 1) / 2
                                        if (max(px1, px2)+pad >= left and
                                            min(px1, px2)-pad <= right and
                                            max(py1, py2)+pad >= top and
                                            min(py1, py2)-pad <= bottom):
                                            targets.append(prior["id"])
                                    entry["targets"] = targets
                                room["strokes"].append(entry)
                                room["previews"].pop(username, None)
                                packet = {"type": "stroke", "stroke": entry}
                            else:
                                content = str(msg.get("text", "")).strip()[:500]
                                if not content:
                                    continue
                                entry = {
                                    "id": event_id, "user": username,
                                    "text": content,
                                    "time": datetime.now().strftime("%H:%M")
                                }
                                room["chat"].append(entry)
                                packet = {"type": "chat", "entry": entry}

                            room["ids"].append(event_id)
                            room["redo"].clear()
                            save_room(code)
                            if action == "stroke" and entry["shape"] in ("eraser","object_edit","object_delete"):
                                broadcast(room, state(room))
                            else:
                                broadcast(room, packet)
                            send(sock, {"type": "ack", "id": event_id})
                            continue

                        if action == "undo" and (not room["locked"] or role == "host"):
                            strokes = room["strokes"]
                            for i in range(len(strokes) - 1, -1, -1):
                                if strokes[i]["user"] != username:
                                    continue
                                group = strokes[i].get("group")
                                if group:
                                    indices = [j for j, s in enumerate(strokes)
                                               if s.get("user") == username
                                               and s.get("group") == group]
                                else:
                                    indices = [i]
                                removed = [strokes[j] for j in indices]
                                for j in reversed(indices):
                                    strokes.pop(j)
                                room["redo"].append(removed)
                                save_room(code)
                                broadcast(room, state(room))
                                break

                        elif action == "redo" and (not room["locked"] or role == "host"):
                            for i in range(len(room["redo"]) - 1, -1, -1):
                                items = room["redo"][i]
                                if isinstance(items, dict):
                                    items = [items]
                                if items and items[0].get("user") == username:
                                    room["redo"].pop(i)
                                    room["strokes"].extend(items)
                                    save_room(code)
                                    broadcast(room, state(room))
                                    break

                        elif action == "clear" and room["owner"] == username:
                            room["strokes"].clear()
                            room["redo"].clear()
                            room["previews"].clear()
                            save_room(code)
                            broadcast(room, state(room))
                            broadcast(room, {"type": "clear_previews"})

                        elif action == "lock" and room["owner"] == username:
                            room["locked"] = bool(msg.get("locked"))
                            room["previews"].clear()
                            save_room(code)
                            broadcast(room, {
                                "type": "locked", "locked": room["locked"]
                            })
                            broadcast(room, {"type": "clear_previews"})

                        elif action == "save":
                            save_room(code)
                            send(sock, {"type": "info", "message": "Board saved"})

                        elif action == "remove_user" and role == "host":
                            target_name = str(msg.get("username", ""))
                            if target_name in (username, room["owner"]):
                                continue
                            target = next(
                                (c for c, n in room["users"].items() if n == target_name),
                                None
                            )
                            if target:
                                if target_name not in room["banned"]:
                                    room["banned"].append(target_name)
                                save_room(code)
                                send(target, {
                                    "type": "removed",
                                    "message": "You were removed by a host"
                                })
                                remove(target, code)
                                try:
                                    target.shutdown(socket.SHUT_RDWR)
                                except OSError:
                                    pass

                        elif action == "end_meeting" and room["owner"] == username:
                            broadcast(room, {
                                "type": "meeting_ended",
                                "message": "Host ended meeting"
                            })
                            room["ended"] = True
                            save_room(code)
                            del rooms[code]
                            code = None
                            break

                except (ValueError, TypeError, KeyError):
                    send(sock, {"type": "error", "message": "Invalid request"})

    except (OSError, UnicodeError):
        pass
    finally:
        with lock:
            remove(sock, code)
            clients.pop(sock, None)
        try:
            sock.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        sock.close()
        print(username or address, "disconnected")

if __name__ == "__main__":
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as server:
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.bind((HOST, PORT))
        server.listen()
        print("Whiteboard server running on port", PORT)
        while True:
            sock, address = server.accept()
            threading.Thread(
                target=handle, args=(sock, address), daemon=True
            ).start()