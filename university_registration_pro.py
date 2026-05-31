"""
============================================================
  SMIU - University Course Registration System PRO
  DSA Project | Department of Artificial Intelligence
  
  Features:
  - Tkinter GUI
  - Linked List  (enrolled courses)
  - Stack        (undo/redo)
  - Queue        (waitlist)
  - BST          (fast student lookup)
  - BFS          (shortest prereq path)
  - DFS          (prereq validation + degree map)
  - Dijkstra     (easiest credit path to degree)
  - Priority Queue (merit-based waitlist)
  - Conflict Detection (timetable clash)
  - CSV save/load
  - Gemini AI Academic Advisor
============================================================
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import csv, os, json, heapq, threading, urllib.request, urllib.error
from collections import deque

# ─── GEMINI AI CONFIG ──────────────────────────────────────
GEMINI_API_KEY  = "AIzaSyBcoEtGDjV1H6k-UAuu4Fbed0092x-E2xk"   # <-- Paste your Gemini API key here
GEMINI_API_URL  = "https://generativelanguage.googleapis.com/v1beta/models/gemini-2.0-flash:generateContent"

# ══════════════════════════════════════════════════════════════
#  DSA DATA STRUCTURES
# ══════════════════════════════════════════════════════════════

# ── 1. LINKED LIST ─────────────────────────────────────────
class CourseNode:
    def __init__(self, code, name, credits, slot):
        self.code    = code
        self.name    = name
        self.credits = credits
        self.slot    = slot   # e.g. "MON-08:00"
        self.next    = None

class EnrolledList:
    def __init__(self):
        self.head  = None
        self.count = 0

    def enroll(self, code, name, credits, slot):
        node = CourseNode(code, name, credits, slot)
        if not self.head:
            self.head = node
        else:
            cur = self.head
            while cur.next:
                cur = cur.next
            cur.next = node
        self.count += 1

    def drop(self, code):
        if not self.head: return False
        if self.head.code == code:
            self.head = self.head.next
            self.count -= 1
            return True
        cur = self.head
        while cur.next:
            if cur.next.code == code:
                cur.next = cur.next.next
                self.count -= 1
                return True
            cur = cur.next
        return False

    def has(self, code):
        cur = self.head
        while cur:
            if cur.code == code: return True
            cur = cur.next
        return False

    def all_slots(self):
        slots, cur = [], self.head
        while cur:
            slots.append(cur.slot)
            cur = cur.next
        return slots

    def total_credits(self):
        t, cur = 0, self.head
        while cur:
            t += cur.credits
            cur = cur.next
        return t

    def to_list(self):
        items, cur = [], self.head
        while cur:
            items.append((cur.code, cur.name, cur.credits, cur.slot))
            cur = cur.next
        return items


# ── 2. STACK (Undo/Redo) ───────────────────────────────────
class UndoStack:
    def __init__(self):
        self._s = []
    def push(self, op, code, name, credits, slot):
        self._s.append((op, code, name, credits, slot))
    def pop(self):
        return self._s.pop() if self._s else None
    def empty(self):
        return len(self._s) == 0


# ── 3. PRIORITY QUEUE (Merit-based waitlist) ───────────────
class MeritWaitlist:
    """
    Min-heap on (-cgpa, arrival_order) so highest CGPA
    gets the next seat.  Lower negative = higher CGPA.
    """
    def __init__(self, capacity=30):
        self.capacity    = capacity
        self.enrolled    = 0
        self._heap       = []
        self._counter    = 0

    def is_full(self):
        return self.enrolled >= self.capacity

    def add(self, roll_no, cgpa):
        heapq.heappush(self._heap, (-cgpa, self._counter, roll_no))
        self._counter += 1

    def admit_next(self):
        if self._heap:
            _, _, roll_no = heapq.heappop(self._heap)
            return roll_no
        return None

    def position(self, roll_no):
        sorted_heap = sorted(self._heap)
        for i, (_, _, r) in enumerate(sorted_heap):
            if r == roll_no:
                return i + 1
        return -1

    def size(self): return len(self._heap)


# ── 4. BST (Fast student lookup by roll number) ────────────
class BSTNode:
    def __init__(self, roll_no, student):
        self.roll_no = roll_no
        self.student = student
        self.left    = None
        self.right   = None

class StudentBST:
    def __init__(self):
        self.root = None

    def insert(self, roll_no, student):
        self.root = self._ins(self.root, roll_no, student)

    def _ins(self, node, roll_no, student):
        if not node:
            return BSTNode(roll_no, student)
        if roll_no < node.roll_no:
            node.left  = self._ins(node.left,  roll_no, student)
        elif roll_no > node.roll_no:
            node.right = self._ins(node.right, roll_no, student)
        else:
            node.student = student   # update
        return node

    def search(self, roll_no):
        node = self.root
        while node:
            if roll_no == node.roll_no: return node.student
            elif roll_no < node.roll_no: node = node.left
            else: node = node.right
        return None

    def inorder(self):
        result = []
        self._inorder(self.root, result)
        return result

    def _inorder(self, node, result):
        if node:
            self._inorder(node.left, result)
            result.append(node.student)
            self._inorder(node.right, result)

    def delete(self, roll_no):
        self.root = self._del(self.root, roll_no)

    def _del(self, node, roll_no):
        if not node: return None
        if roll_no < node.roll_no:
            node.left  = self._del(node.left,  roll_no)
        elif roll_no > node.roll_no:
            node.right = self._del(node.right, roll_no)
        else:
            if not node.left:  return node.right
            if not node.right: return node.left
            # find inorder successor
            suc = node.right
            while suc.left: suc = suc.left
            node.roll_no = suc.roll_no
            node.student = suc.student
            node.right   = self._del(node.right, suc.roll_no)
        return node


# ── 5. COURSE GRAPH  (BFS / DFS / Dijkstra) ───────────────
class CourseGraph:
    def __init__(self):
        # adjacency: prereq -> [(course, weight=credits)]
        self.adj   = {}
        # reverse: course -> [prereqs]
        self.rev   = {}

    def add_course(self, code):
        self.adj.setdefault(code, [])
        self.rev.setdefault(code, [])

    def add_prereq(self, prereq, course, weight=1):
        self.add_course(prereq)
        self.add_course(course)
        self.adj[prereq].append((course, weight))
        self.rev[course].append(prereq)

    # BFS – shortest hop path
    def bfs_path(self, start, target):
        if start not in self.adj: return []
        q, visited = deque([[start]]), set()
        while q:
            path = q.popleft()
            node = path[-1]
            if node == target: return path
            if node not in visited:
                visited.add(node)
                for nb, _ in self.adj.get(node, []):
                    q.append(path + [nb])
        return []

    # DFS – all courses reachable
    def dfs_reachable(self, start, visited=None):
        if visited is None: visited = set()
        visited.add(start)
        for nb, _ in self.adj.get(start, []):
            if nb not in visited:
                self.dfs_reachable(nb, visited)
        return visited

    # DFS – check all prereqs met
    def prereqs_met(self, target, completed):
        def check(course, seen):
            seen.add(course)
            for p in self.rev.get(course, []):
                if p not in seen:
                    if p not in completed: return False
                    if not check(p, seen): return False
            return True
        return check(target, set())

    # Dijkstra – path with minimum total credits
    def dijkstra_easiest(self, start, target):
        # weight = credits of destination course
        dist  = {start: 0}
        prev  = {start: None}
        pq    = [(0, start)]
        while pq:
            cost, node = heapq.heappop(pq)
            if node == target:
                # rebuild path
                path = []
                while node:
                    path.append(node)
                    node = prev[node]
                return list(reversed(path)), cost
            for nb, w in self.adj.get(node, []):
                nc = cost + w
                if nc < dist.get(nb, float('inf')):
                    dist[nb] = nc
                    prev[nb] = node
                    heapq.heappush(pq, (nc, nb))
        return [], -1


# ── 6. CONFLICT DETECTION ──────────────────────────────────
def has_conflict(existing_slots, new_slot):
    """Return True if new_slot clashes with any existing slot."""
    return new_slot in existing_slots


# ══════════════════════════════════════════════════════════════
#  STUDENT MODEL
# ══════════════════════════════════════════════════════════════
class Student:
    def __init__(self, roll_no, name, section, cgpa=3.0):
        self.roll_no  = roll_no
        self.name     = name
        self.section  = section
        self.cgpa     = float(cgpa)
        self.courses  = EnrolledList()
        self.undo_stk = UndoStack()


# ══════════════════════════════════════════════════════════════
#  REGISTRATION ENGINE
# ══════════════════════════════════════════════════════════════
class RegistrationSystem:
    CSV_FILE = "students.csv"

    def __init__(self):
        self.bst          = StudentBST()
        self.graph        = CourseGraph()
        self.waitlists    = {}   # code -> MeritWaitlist
        self.course_info  = {}   # code -> {name, credits, slot, capacity}
        self._setup_default_data()
        self.load_csv()

    # ── default courses ────────────────────────────────────
    def _setup_default_data(self):
        courses = [
            ("CS101","Intro to Programming",  3,"MON-08:00",30),
            ("MATH101","Discrete Mathematics",3,"TUE-08:00",30),
            ("CS201","Data Structures",       3,"WED-10:00",30),
            ("CS202","OOP Concepts",          3,"MON-10:00",30),
            ("CS301","Algorithms",            3,"THU-08:00",30),
            ("AI101","Intro to AI",           3,"FRI-08:00",30),
            ("AI201","Machine Learning",      4,"MON-12:00",30),
            ("AI301","Deep Learning",         4,"WED-12:00",30),
            ("CS401","Operating Systems",     3,"TUE-12:00",30),
            ("CS402","Computer Networks",     3,"THU-10:00",30),
        ]
        for code, name, cr, slot, cap in courses:
            self.course_info[code] = {"name":name,"credits":cr,"slot":slot,"capacity":cap}
            self.graph.add_course(code)
            self.waitlists[code]   = MeritWaitlist(cap)

        prereqs = [
            ("CS101","CS201",3),("CS101","CS202",3),
            ("MATH101","CS201",3),("CS201","CS301",3),
            ("CS301","AI101",3),("AI101","AI201",4),
            ("AI201","AI301",4),("CS201","CS401",3),
            ("CS401","CS402",3),
        ]
        for p, c, w in prereqs:
            self.graph.add_prereq(p, c, w)

    # ── CSV persistence ────────────────────────────────────
    def save_csv(self):
        students = self.bst.inorder()
        with open(self.CSV_FILE, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["roll_no","name","section","cgpa","courses"])
            for s in students:
                enrolled = json.dumps(s.courses.to_list())
                w.writerow([s.roll_no, s.name, s.section, s.cgpa, enrolled])

    def load_csv(self):
        if not os.path.exists(self.CSV_FILE): return
        with open(self.CSV_FILE, newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                s = Student(row["roll_no"], row["name"],
                            row["section"], float(row["cgpa"]))
                try:
                    courses = json.loads(row["courses"])
                    for code, name, cr, slot in courses:
                        s.courses.enroll(code, name, cr, slot)
                        wl = self.waitlists.get(code)
                        if wl: wl.enrolled += 1
                except Exception:
                    pass
                self.bst.insert(s.roll_no, s)

    # ── student ops ────────────────────────────────────────
    def add_student(self, roll_no, name, section, cgpa=3.0):
        if self.bst.search(roll_no):
            return False, "Student already exists."
        s = Student(roll_no, name, section, cgpa)
        self.bst.insert(roll_no, s)
        self.save_csv()
        return True, f"Student {name} added."

    def get_student(self, roll_no):
        return self.bst.search(roll_no)

    def all_students(self):
        return self.bst.inorder()

    # ── enroll ─────────────────────────────────────────────
    def enroll(self, roll_no, code):
        s = self.bst.search(roll_no)
        if not s: return False, "Student not found."
        if code not in self.course_info: return False, "Course not found."
        if s.courses.has(code): return False, "Already enrolled."

        # prereq check (DFS)
        completed = {c for c,*_ in s.courses.to_list()}
        if not self.graph.prereqs_met(code, completed):
            return False, "Prerequisites not met."

        # conflict check
        info     = self.course_info[code]
        existing = s.courses.all_slots()
        if has_conflict(existing, info["slot"]):
            return False, f"Timetable clash! Slot {info['slot']} already occupied."

        wl = self.waitlists[code]
        if wl.is_full():
            wl.add(roll_no, s.cgpa)
            pos = wl.position(roll_no)
            return False, f"Course full. Waitlisted at position #{pos} (merit-based)."

        s.courses.enroll(code, info["name"], info["credits"], info["slot"])
        wl.enrolled += 1
        s.undo_stk.push("ENROLL", code, info["name"], info["credits"], info["slot"])
        self.save_csv()
        return True, f"Enrolled in {code} — {info['name']}."

    # ── drop ───────────────────────────────────────────────
    def drop(self, roll_no, code):
        s = self.bst.search(roll_no)
        if not s: return False, "Student not found."
        info = self.course_info.get(code, {})
        if s.courses.drop(code):
            s.undo_stk.push("DROP", code, info.get("name",""),
                            info.get("credits",0), info.get("slot",""))
            wl = self.waitlists[code]
            wl.enrolled -= 1
            msg = f"Dropped {code}."
            next_r = wl.admit_next()
            if next_r:
                ns = self.bst.search(next_r)
                if ns:
                    ns.courses.enroll(code, info["name"], info["credits"], info["slot"])
                    wl.enrolled += 1
                    msg += f" Seat given to {next_r} (merit admit)."
            self.save_csv()
            return True, msg
        return False, "Not enrolled in this course."

    # ── undo ───────────────────────────────────────────────
    def undo(self, roll_no):
        s = self.bst.search(roll_no)
        if not s or s.undo_stk.empty(): return False, "Nothing to undo."
        op, code, name, cr, slot = s.undo_stk.pop()
        if op == "ENROLL":
            s.courses.drop(code)
            self.waitlists[code].enrolled -= 1
            self.save_csv()
            return True, f"Undone: removed from {code}."
        else:
            s.courses.enroll(code, name, cr, slot)
            self.waitlists[code].enrolled += 1
            self.save_csv()
            return True, f"Undone: re-enrolled in {code}."

    # ── path queries ───────────────────────────────────────
    def bfs_path(self, a, b):
        return self.graph.bfs_path(a, b)

    def dijkstra_path(self, a, b):
        return self.graph.dijkstra_easiest(a, b)

    def dfs_map(self, start):
        return self.graph.dfs_reachable(start) - {start}


# ══════════════════════════════════════════════════════════════
#  GEMINI AI ADVISOR
# ══════════════════════════════════════════════════════════════
def ask_gemini(prompt, callback):
    """
    Calls Gemini 2.0 Flash via REST (no SDK needed).
    Runs in a background thread so UI stays responsive.
    callback(text) is called with the response.
    """
    def _call():
        if not GEMINI_API_KEY:
            callback("⚠  No API key set.\nOpen university_registration_pro.py and paste "
                     "your Gemini API key in the GEMINI_API_KEY variable at the top.")
            return
        payload = json.dumps({
            "contents": [{"parts": [{"text": prompt}]}]
        }).encode("utf-8")
        req = urllib.request.Request(
            f"{GEMINI_API_URL}?key={GEMINI_API_KEY}",
            data=payload,
            headers={"Content-Type": "application/json"},
            method="POST"
        )
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                data = json.loads(resp.read().decode())
                text = data["candidates"][0]["content"]["parts"][0]["text"]
                callback(text)
        except urllib.error.HTTPError as e:
            body = e.read().decode()
            callback(f"API Error {e.code}: {body}")
        except Exception as ex:
            callback(f"Error: {ex}")
    threading.Thread(target=_call, daemon=True).start()


# ══════════════════════════════════════════════════════════════
#  TKINTER GUI
# ══════════════════════════════════════════════════════════════
BLUE   = "#2563eb"
DARK   = "#1e293b"
WHITE  = "#ffffff"
BG     = "#f8fafc"
CARD   = "#ffffff"
MUTED  = "#64748b"
GREEN  = "#16a34a"
RED    = "#dc2626"
PURPLE = "#7c3aed"
AMBER  = "#d97706"

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("SMIU Course Registration System — AI Edition")
        self.geometry("1200x750")
        self.configure(bg=BG)
        self.resizable(True, True)
        self.sys = RegistrationSystem()
        self._build_ui()

    # ── main layout ────────────────────────────────────────
    def _build_ui(self):
        # sidebar
        sb = tk.Frame(self, bg=DARK, width=200)
        sb.pack(side="left", fill="y")
        sb.pack_propagate(False)

        tk.Label(sb, text="SMIU", bg=DARK, fg=WHITE,
                 font=("Helvetica",18,"bold")).pack(pady=(24,2))
        tk.Label(sb, text="Registration System", bg=DARK, fg="#94a3b8",
                 font=("Helvetica",9)).pack(pady=(0,24))

        self._pages = {}
        nav_items = [
            ("Dashboard",    self._page_dashboard),
            ("Students",     self._page_students),
            ("Enrollment",   self._page_enrollment),
            ("Course Paths", self._page_paths),
            ("AI Advisor",   self._page_ai),
        ]
        self._nav_btns = []
        self._content  = tk.Frame(self, bg=BG)
        self._content.pack(side="left", fill="both", expand=True)

        for label, builder in nav_items:
            btn = tk.Button(sb, text=label, bg=DARK, fg="#cbd5e1",
                            font=("Helvetica",11), relief="flat",
                            activebackground="#334155", activeforeground=WHITE,
                            anchor="w", padx=20, cursor="hand2",
                            command=lambda b=builder, l=label: self._switch(l, b))
            btn.pack(fill="x", pady=1)
            self._nav_btns.append((label, btn))

        self._switch("Dashboard", self._page_dashboard)

    def _switch(self, label, builder):
        for w in self._content.winfo_children():
            w.destroy()
        for lbl, btn in self._nav_btns:
            btn.config(bg=BLUE if lbl == label else DARK,
                       fg=WHITE if lbl == label else "#cbd5e1")
        builder()

    # ── helper widgets ─────────────────────────────────────
    def _card(self, parent, **kw):
        f = tk.Frame(parent, bg=CARD, relief="flat",
                     highlightbackground="#e2e8f0", highlightthickness=1, **kw)
        return f

    def _label(self, p, text, size=11, bold=False, color=DARK, **kw):
        font = ("Helvetica", size, "bold" if bold else "normal")
        return tk.Label(p, text=text, bg=p.cget("bg"), fg=color,
                        font=font, **kw)

    def _btn(self, p, text, cmd, color=BLUE, fg=WHITE, **kw):
        return tk.Button(p, text=text, command=cmd,
                         bg=color, fg=fg, font=("Helvetica",10,"bold"),
                         relief="flat", padx=12, pady=6, cursor="hand2",
                         activebackground=color, activeforeground=fg, **kw)

    def _entry_row(self, parent, label, row, default=""):
        tk.Label(parent, text=label, bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).grid(row=row, column=0, sticky="w", pady=4, padx=8)
        var = tk.StringVar(value=default)
        e   = tk.Entry(parent, textvariable=var, font=("Helvetica",10),
                       relief="solid", bd=1, width=24)
        e.grid(row=row, column=1, pady=4, padx=8, sticky="ew")
        return var

    def _status(self, parent, msg, ok=True):
        color = GREEN if ok else RED
        lbl   = tk.Label(parent, text=msg, bg=CARD, fg=color,
                         font=("Helvetica",10), wraplength=400, justify="left")
        lbl.pack(pady=6, padx=10, anchor="w")
        parent.after(4000, lbl.destroy)

    # ══ PAGE: DASHBOARD ════════════════════════════════════
    def _page_dashboard(self):
        p = self._content
        tk.Label(p, text="Dashboard", bg=BG, fg=DARK,
                 font=("Helvetica",20,"bold")).pack(anchor="w", padx=24, pady=(20,4))
        tk.Label(p, text="SMIU — Department of Artificial Intelligence",
                 bg=BG, fg=MUTED, font=("Helvetica",11)).pack(anchor="w", padx=24)

        stats_frame = tk.Frame(p, bg=BG)
        stats_frame.pack(fill="x", padx=24, pady=16)

        students  = self.sys.all_students()
        n_stu     = len(students)
        n_courses = len(self.sys.course_info)
        total_enr = sum(s.courses.count for s in students)

        for title, val, color in [
            ("Total Students",    n_stu,     BLUE),
            ("Available Courses", n_courses, GREEN),
            ("Total Enrollments", total_enr, PURPLE),
        ]:
            c = tk.Frame(stats_frame, bg=color, width=160, height=90)
            c.pack(side="left", padx=8, pady=4)
            c.pack_propagate(False)
            tk.Label(c, text=str(val), bg=color, fg=WHITE,
                     font=("Helvetica",28,"bold")).pack(pady=(14,0))
            tk.Label(c, text=title, bg=color, fg=WHITE,
                     font=("Helvetica",9)).pack()

        # Course table
        tk.Label(p, text="Available Courses", bg=BG, fg=DARK,
                 font=("Helvetica",14,"bold")).pack(anchor="w", padx=24, pady=(8,4))
        frame = tk.Frame(p, bg=BG)
        frame.pack(fill="both", expand=True, padx=24, pady=4)

        cols = ("Code","Name","Credits","Slot","Enrolled","Capacity","Waitlist")
        tv   = ttk.Treeview(frame, columns=cols, show="headings", height=12)
        for c in cols:
            tv.heading(c, text=c)
            tv.column(c, width=110, anchor="center")
        tv.column("Name", width=200, anchor="w")

        for code, info in self.sys.course_info.items():
            wl = self.sys.waitlists[code]
            tv.insert("", "end", values=(
                code, info["name"], info["credits"], info["slot"],
                wl.enrolled, wl.capacity, wl.size()
            ))
        sb2 = ttk.Scrollbar(frame, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb2.set)
        tv.pack(side="left", fill="both", expand=True)
        sb2.pack(side="right", fill="y")

    # ══ PAGE: STUDENTS ═════════════════════════════════════
    def _page_students(self):
        p = self._content
        tk.Label(p, text="Student Management", bg=BG, fg=DARK,
                 font=("Helvetica",20,"bold")).pack(anchor="w", padx=24, pady=(20,4))

        row_top = tk.Frame(p, bg=BG)
        row_top.pack(fill="x", padx=24, pady=8)

        # Add student card
        card = self._card(row_top, width=340)
        card.pack(side="left", fill="y", padx=(0,16), pady=4)
        card.pack_propagate(False)
        tk.Label(card, text="Add New Student", bg=CARD, fg=DARK,
                 font=("Helvetica",13,"bold")).grid(row=0, column=0, columnspan=2,
                                                     pady=(12,6), padx=8, sticky="w")
        v_roll = self._entry_row(card, "Roll No", 1, "BAI-25S-XXX")
        v_name = self._entry_row(card, "Full Name", 2, "")
        v_sec  = self._entry_row(card, "Section", 3, "3A")
        v_cgpa = self._entry_row(card, "CGPA", 4, "3.0")
        status_frame = tk.Frame(card, bg=CARD)
        status_frame.grid(row=6, column=0, columnspan=2, sticky="ew")

        def do_add():
            ok, msg = self.sys.add_student(
                v_roll.get().strip(), v_name.get().strip(),
                v_sec.get().strip(), v_cgpa.get().strip() or "3.0"
            )
            self._status(status_frame, msg, ok)
            if ok: refresh()

        self._btn(card, "Add Student", do_add).grid(
            row=5, column=0, columnspan=2, pady=10, padx=8, sticky="ew")
        card.grid_columnconfigure(1, weight=1)

        # Search card
        scard = self._card(row_top, width=280)
        scard.pack(side="left", fill="y", pady=4)
        scard.pack_propagate(False)
        tk.Label(scard, text="Search (BST)", bg=CARD, fg=DARK,
                 font=("Helvetica",13,"bold")).pack(anchor="w", padx=12, pady=(12,4))
        v_srch = tk.StringVar()
        tk.Entry(scard, textvariable=v_srch, font=("Helvetica",10),
                 relief="solid", bd=1).pack(fill="x", padx=12, pady=4)
        result_lbl = tk.Label(scard, text="", bg=CARD, fg=DARK,
                              font=("Helvetica",10), justify="left", wraplength=240)
        result_lbl.pack(padx=12, pady=4, anchor="w")

        def do_search():
            s = self.sys.get_student(v_srch.get().strip())
            if s:
                result_lbl.config(
                    fg=GREEN,
                    text=f"Found (BST O(log n)):\n{s.name}\n{s.section} | CGPA {s.cgpa}\n"
                         f"Courses: {s.courses.count}\nCredits: {s.courses.total_credits()}"
                )
            else:
                result_lbl.config(fg=RED, text="Student not found.")

        self._btn(scard, "Search", do_search).pack(padx=12, pady=6, fill="x")

        # Student list
        tk.Label(p, text="All Students (BST In-order)", bg=BG, fg=DARK,
                 font=("Helvetica",13,"bold")).pack(anchor="w", padx=24, pady=(8,2))
        lframe = tk.Frame(p, bg=BG)
        lframe.pack(fill="both", expand=True, padx=24, pady=4)
        cols = ("Roll No","Name","Section","CGPA","Courses","Credits")
        tv   = ttk.Treeview(lframe, columns=cols, show="headings", height=10)
        for c in cols:
            tv.heading(c, text=c)
            tv.column(c, width=130, anchor="center")
        tv.column("Name", width=180, anchor="w")
        sb2 = ttk.Scrollbar(lframe, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb2.set)
        tv.pack(side="left", fill="both", expand=True)
        sb2.pack(side="right", fill="y")

        def refresh():
            tv.delete(*tv.get_children())
            for s in self.sys.all_students():
                tv.insert("", "end", values=(
                    s.roll_no, s.name, s.section, f"{s.cgpa:.1f}",
                    s.courses.count, s.courses.total_credits()
                ))
        refresh()

    # ══ PAGE: ENROLLMENT ═══════════════════════════════════
    def _page_enrollment(self):
        p = self._content
        tk.Label(p, text="Course Enrollment", bg=BG, fg=DARK,
                 font=("Helvetica",20,"bold")).pack(anchor="w", padx=24, pady=(20,4))

        top = tk.Frame(p, bg=BG)
        top.pack(fill="x", padx=24, pady=8)

        # Enroll card
        ec = self._card(top, width=320)
        ec.pack(side="left", fill="y", padx=(0,12))
        ec.pack_propagate(False)
        tk.Label(ec, text="Enroll / Drop", bg=CARD, fg=DARK,
                 font=("Helvetica",13,"bold")).pack(anchor="w", padx=12, pady=(12,4))

        tk.Label(ec, text="Roll No", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12)
        v_roll = tk.StringVar()
        tk.Entry(ec, textvariable=v_roll, font=("Helvetica",10),
                 relief="solid", bd=1, width=28).pack(padx=12, pady=4, fill="x")

        tk.Label(ec, text="Course Code", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12)
        v_code = tk.StringVar()
        course_cb = ttk.Combobox(ec, textvariable=v_code, width=26,
                                  values=list(self.sys.course_info.keys()))
        course_cb.pack(padx=12, pady=4, fill="x")

        status_f = tk.Frame(ec, bg=CARD)
        status_f.pack(fill="x", padx=12)

        def do_enroll():
            ok, msg = self.sys.enroll(v_roll.get().strip(), v_code.get().strip())
            self._status(status_f, msg, ok)
            refresh_student()

        def do_drop():
            ok, msg = self.sys.drop(v_roll.get().strip(), v_code.get().strip())
            self._status(status_f, msg, ok)
            refresh_student()

        def do_undo():
            ok, msg = self.sys.undo(v_roll.get().strip())
            self._status(status_f, msg, ok)
            refresh_student()

        btn_row = tk.Frame(ec, bg=CARD)
        btn_row.pack(fill="x", padx=12, pady=8)
        self._btn(btn_row, "Enroll", do_enroll, GREEN).pack(side="left", padx=4)
        self._btn(btn_row, "Drop",   do_drop,   RED).pack(side="left", padx=4)
        self._btn(btn_row, "Undo",   do_undo,   AMBER).pack(side="left", padx=4)

        # Student courses card
        sc = self._card(top)
        sc.pack(side="left", fill="both", expand=True)
        tk.Label(sc, text="Student's Enrolled Courses (Linked List)",
                 bg=CARD, fg=DARK, font=("Helvetica",13,"bold")).pack(
                     anchor="w", padx=12, pady=(12,4))
        cols = ("Code","Name","Credits","Slot")
        stv  = ttk.Treeview(sc, columns=cols, show="headings", height=6)
        for c in cols:
            stv.heading(c, text=c)
            stv.column(c, anchor="center", width=120)
        stv.column("Name", width=200, anchor="w")
        stv.pack(fill="both", expand=True, padx=12, pady=4)
        cred_lbl = tk.Label(sc, text="Total credits: 0", bg=CARD, fg=MUTED,
                            font=("Helvetica",10))
        cred_lbl.pack(anchor="w", padx=12, pady=4)

        def refresh_student():
            stv.delete(*stv.get_children())
            s = self.sys.get_student(v_roll.get().strip())
            if s:
                for code, name, cr, slot in s.courses.to_list():
                    stv.insert("", "end", values=(code, name, cr, slot))
                cred_lbl.config(text=f"Total credits: {s.courses.total_credits()} | "
                                     f"CGPA: {s.cgpa:.1f}")

        v_roll.trace_add("write", lambda *_: refresh_student())

        # Conflict + waitlist info panel
        info_f = tk.Frame(p, bg=BG)
        info_f.pack(fill="x", padx=24, pady=8)
        tk.Label(info_f, text="Course Info & Waitlists", bg=BG, fg=DARK,
                 font=("Helvetica",13,"bold")).pack(anchor="w", pady=(0,4))
        cols2 = ("Course","Name","Slot","Enrolled","Capacity","Waitlist Size")
        tv2   = ttk.Treeview(info_f, columns=cols2, show="headings", height=6)
        for c in cols2:
            tv2.heading(c, text=c)
            tv2.column(c, anchor="center", width=120)
        tv2.column("Name", width=180, anchor="w")
        for code, info in self.sys.course_info.items():
            wl = self.sys.waitlists[code]
            tv2.insert("", "end", values=(
                code, info["name"], info["slot"],
                wl.enrolled, wl.capacity, wl.size()
            ))
        tv2.pack(fill="x")

    # ══ PAGE: COURSE PATHS ═════════════════════════════════
    def _page_paths(self):
        p = self._content
        tk.Label(p, text="Course Paths & Prerequisites",
                 bg=BG, fg=DARK, font=("Helvetica",20,"bold")).pack(
                     anchor="w", padx=24, pady=(20,4))

        top = tk.Frame(p, bg=BG)
        top.pack(fill="x", padx=24, pady=8)

        # BFS card
        bfs_c = self._card(top, width=360)
        bfs_c.pack(side="left", fill="y", padx=(0,12))
        bfs_c.pack_propagate(False)
        tk.Label(bfs_c, text="BFS — Shortest Prerequisite Path",
                 bg=CARD, fg=BLUE, font=("Helvetica",12,"bold")).pack(
                     anchor="w", padx=12, pady=(12,4))
        tk.Label(bfs_c, text="Fewest hops between two courses",
                 bg=CARD, fg=MUTED, font=("Helvetica",9)).pack(anchor="w", padx=12)
        tk.Label(bfs_c, text="From", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12, pady=(8,0))
        v_bfs_a = tk.StringVar(value="CS101")
        ttk.Combobox(bfs_c, textvariable=v_bfs_a,
                     values=list(self.sys.course_info.keys()),
                     width=28).pack(padx=12, fill="x")
        tk.Label(bfs_c, text="To", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12, pady=(6,0))
        v_bfs_b = tk.StringVar(value="AI201")
        ttk.Combobox(bfs_c, textvariable=v_bfs_b,
                     values=list(self.sys.course_info.keys()),
                     width=28).pack(padx=12, fill="x")
        bfs_res = tk.Label(bfs_c, text="", bg=CARD, fg=DARK,
                           font=("Courier",10), wraplength=320, justify="left")
        bfs_res.pack(padx=12, pady=6, anchor="w")

        def do_bfs():
            path = self.sys.bfs_path(v_bfs_a.get(), v_bfs_b.get())
            if path:
                bfs_res.config(fg=GREEN, text=" → ".join(path))
            else:
                bfs_res.config(fg=RED, text="No path found.")

        self._btn(bfs_c, "Find BFS Path", do_bfs).pack(padx=12, pady=8, fill="x")

        # Dijkstra card
        dij_c = self._card(top, width=360)
        dij_c.pack(side="left", fill="y", padx=(0,12))
        dij_c.pack_propagate(False)
        tk.Label(dij_c, text="Dijkstra — Easiest Credit Path",
                 bg=CARD, fg=PURPLE, font=("Helvetica",12,"bold")).pack(
                     anchor="w", padx=12, pady=(12,4))
        tk.Label(dij_c, text="Minimum total credits to reach a course",
                 bg=CARD, fg=MUTED, font=("Helvetica",9)).pack(anchor="w", padx=12)
        tk.Label(dij_c, text="From", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12, pady=(8,0))
        v_dij_a = tk.StringVar(value="CS101")
        ttk.Combobox(dij_c, textvariable=v_dij_a,
                     values=list(self.sys.course_info.keys()),
                     width=28).pack(padx=12, fill="x")
        tk.Label(dij_c, text="To", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12, pady=(6,0))
        v_dij_b = tk.StringVar(value="AI301")
        ttk.Combobox(dij_c, textvariable=v_dij_b,
                     values=list(self.sys.course_info.keys()),
                     width=28).pack(padx=12, fill="x")
        dij_res = tk.Label(dij_c, text="", bg=CARD, fg=DARK,
                           font=("Courier",10), wraplength=320, justify="left")
        dij_res.pack(padx=12, pady=6, anchor="w")

        def do_dijkstra():
            path, cost = self.sys.dijkstra_path(v_dij_a.get(), v_dij_b.get())
            if path:
                dij_res.config(fg=PURPLE,
                    text=" → ".join(path) + f"\nTotal credits: {cost}")
            else:
                dij_res.config(fg=RED, text="No path found.")

        self._btn(dij_c, "Find Easiest Path", do_dijkstra,
                  PURPLE).pack(padx=12, pady=8, fill="x")

        # DFS card
        dfs_c = self._card(top)
        dfs_c.pack(side="left", fill="both", expand=True)
        tk.Label(dfs_c, text="DFS — Full Degree Map",
                 bg=CARD, fg=AMBER, font=("Helvetica",12,"bold")).pack(
                     anchor="w", padx=12, pady=(12,4))
        tk.Label(dfs_c, text="All courses reachable from a starting course",
                 bg=CARD, fg=MUTED, font=("Helvetica",9)).pack(anchor="w", padx=12)
        tk.Label(dfs_c, text="Start", bg=CARD, fg=MUTED,
                 font=("Helvetica",10)).pack(anchor="w", padx=12, pady=(8,0))
        v_dfs = tk.StringVar(value="CS101")
        ttk.Combobox(dfs_c, textvariable=v_dfs,
                     values=list(self.sys.course_info.keys()),
                     width=24).pack(padx=12, fill="x")
        dfs_txt = scrolledtext.ScrolledText(dfs_c, height=8, font=("Courier",10),
                                            relief="flat", bg=BG)
        dfs_txt.pack(fill="both", expand=True, padx=12, pady=6)

        def do_dfs():
            reachable = self.sys.dfs_map(v_dfs.get())
            dfs_txt.config(state="normal")
            dfs_txt.delete("1.0","end")
            for code in sorted(reachable):
                info = self.sys.course_info.get(code, {})
                dfs_txt.insert("end",
                    f"  {code}  —  {info.get('name','')}  ({info.get('credits','')} cr)\n")
            dfs_txt.config(state="disabled")

        self._btn(dfs_c, "Run DFS", do_dfs, AMBER).pack(padx=12, pady=4, fill="x")

    # ══ PAGE: AI ADVISOR ═══════════════════════════════════
    def _page_ai(self):
        p = self._content
        tk.Label(p, text="Gemini AI Academic Advisor",
                 bg=BG, fg=DARK, font=("Helvetica",20,"bold")).pack(
                     anchor="w", padx=24, pady=(20,2))
        tk.Label(p, text="Powered by Gemini 2.0 Flash  •  REST API (no SDK)",
                 bg=BG, fg=MUTED, font=("Helvetica",10)).pack(anchor="w", padx=24)

        top = tk.Frame(p, bg=BG)
        top.pack(fill="x", padx=24, pady=10)

        # Quick prompts
        qp = self._card(top, width=280)
        qp.pack(side="left", fill="y", padx=(0,12))
        qp.pack_propagate(False)
        tk.Label(qp, text="Quick Prompts", bg=CARD, fg=DARK,
                 font=("Helvetica",12,"bold")).pack(anchor="w", padx=12, pady=(12,6))

        def build_context():
            students = self.sys.all_students()
            ctx  = "You are an academic advisor at SMIU (Sindh Madressatul Islam University).\n"
            ctx += f"There are {len(students)} students registered.\n"
            ctx += "Courses available: " + ", ".join(self.sys.course_info.keys()) + ".\n"
            ctx += "Prerequisite chains: CS101->CS201->CS301->AI101->AI201->AI301.\n"
            return ctx

        quick_prompts = [
            ("Course Plan for AI Degree",
             lambda: build_context() + " Give a semester-by-semester course plan for a student wanting to specialize in AI, covering all prerequisites in order. Be concise."),
            ("Suggest Courses for Student",
             lambda: build_context() + f" Student roll {v_roll.get().strip()} has completed these courses. Suggest the best 3 next courses to take and explain why briefly."),
            ("Explain BFS vs Dijkstra",
             lambda: "Explain in simple terms the difference between BFS and Dijkstra's algorithm in the context of finding paths in a university course prerequisite graph. Use a short example."),
            ("Study Tips for DSA",
             lambda: "Give 5 practical study tips for a university student preparing for a Data Structures & Algorithms exam covering linked lists, stacks, queues, BFS, DFS, and trees."),
            ("Merit Waitlist Explained",
             lambda: "Explain in simple terms how a priority queue works for a merit-based waitlist in a course registration system. Use a short analogy."),
        ]

        chat_box = scrolledtext.ScrolledText(p, height=16, font=("Helvetica",11),
                                             relief="flat", bg=CARD,
                                             wrap="word", state="disabled")

        def send_prompt(prompt_fn):
            prompt = prompt_fn()
            _append_chat("You", prompt[:120] + ("..." if len(prompt) > 120 else ""), BLUE)
            _append_chat("Gemini", "Thinking...", MUTED)
            def cb(text):
                chat_box.config(state="normal")
                # replace last "Thinking..." entry
                chat_box.delete("end-3l", "end-1l")
                chat_box.config(state="disabled")
                _append_chat("Gemini AI", text, PURPLE)
            ask_gemini(prompt, cb)

        for label, pfn in quick_prompts:
            self._btn(qp, label, lambda f=pfn: send_prompt(f),
                      "#f1f5f9", DARK).pack(fill="x", padx=8, pady=3)

        # Roll for context
        tk.Label(qp, text="Student roll (for suggestions):",
                 bg=CARD, fg=MUTED, font=("Helvetica",9)).pack(anchor="w", padx=12, pady=(10,0))
        v_roll = tk.StringVar(value="BAI-25S-001")
        tk.Entry(qp, textvariable=v_roll, font=("Helvetica",10),
                 relief="solid", bd=1).pack(padx=12, fill="x", pady=4)

        # Chat area
        chat_frame = tk.Frame(top, bg=BG)
        chat_frame.pack(side="left", fill="both", expand=True)
        tk.Label(chat_frame, text="Chat", bg=BG, fg=DARK,
                 font=("Helvetica",12,"bold")).pack(anchor="w", pady=(0,4))

        chat_box.pack(in_=chat_frame, fill="both", expand=True)

        # Custom input
        inp_row = tk.Frame(p, bg=BG)
        inp_row.pack(fill="x", padx=24, pady=8)
        v_inp = tk.StringVar()
        tk.Entry(inp_row, textvariable=v_inp, font=("Helvetica",11),
                 relief="solid", bd=1).pack(side="left", fill="x", expand=True, padx=(0,8))

        def send_custom():
            q = v_inp.get().strip()
            if not q: return
            v_inp.set("")
            ctx = build_context()
            send_prompt(lambda c=ctx, qq=q: c + "\n\nStudent question: " + qq)

        self._btn(inp_row, "Ask Gemini ↗", send_custom).pack(side="left")
        self.bind("<Return>", lambda e: send_custom())

        def _append_chat(sender, text, color):
            chat_box.config(state="normal")
            chat_box.insert("end", f"\n{sender}:\n", f"sender_{color}")
            chat_box.insert("end", text + "\n", "body")
            chat_box.tag_config(f"sender_{color}", foreground=color,
                                font=("Helvetica",10,"bold"))
            chat_box.tag_config("body", font=("Helvetica",10))
            chat_box.see("end")
            chat_box.config(state="disabled")

        _append_chat("System",
            "Welcome! Click a quick prompt on the left or type your own question below.\n"
            "Make sure your Gemini API key is set in university_registration_pro.py.", MUTED)


# ══════════════════════════════════════════════════════════════
if __name__ == "__main__":
    app = App()
    app.mainloop()
