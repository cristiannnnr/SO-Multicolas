import tkinter as tk
from tkinter import ttk, messagebox
import random
import threading
import time
import collections

# --- ESTRUCTURAS DE DATOS Y LÓGICA (importar o copiar del archivo original) ---
# Aquí solo se deja la definición de Proceso y la lista master_procesos para la gestión de procesos

class Proceso:
    def _init_(self, id_proceso, tiempo_llegada, tiempo_rafaga, priority=None, queue_type=None):
        self.id = id_proceso
        self.t_llegada = tiempo_llegada
        self.bt = tiempo_rafaga
        self.original_at = tiempo_llegada
        self.original_bt = tiempo_rafaga
        self.priority = priority
        self.queue_type = queue_type
        self.siguiente = None  # Necesario para ListaCircular
        self.entry_time_to_queue: float = 0.0  # Para envejecimiento y llegada en tiempo real

master_procesos = []  # Lista de todos los procesos agregados al sistema

# --- Lógica de simulación y estructuras de datos (copiadas del original, simplificadas para integración) ---

class ListaCircular:
    def _init_(self):
        self.ultimo = None
    def esta_vacia(self):
        return self.ultimo is None
    def encolar_proceso(self, nuevo_proceso):
        if self.esta_vacia():
            self.ultimo = nuevo_proceso
            nuevo_proceso.siguiente = nuevo_proceso
        else:
            if self.ultimo is not None and self.ultimo.siguiente is not None:
                nuevo_proceso.siguiente = self.ultimo.siguiente
            else:
                nuevo_proceso.siguiente = nuevo_proceso
            self.ultimo.siguiente = nuevo_proceso
            self.ultimo = nuevo_proceso
    def desencolar_proceso_rr(self):
        if self.esta_vacia() or self.ultimo is None or self.ultimo.siguiente is None:
            return None
        proceso_a_ejecutar = self.ultimo.siguiente
        if self.ultimo == self.ultimo.siguiente:
            self.ultimo = None
        else:
            if self.ultimo.siguiente is not None:
                self.ultimo.siguiente = proceso_a_ejecutar.siguiente
        return proceso_a_ejecutar
    def obtener_procesos_en_orden(self):
        if self.esta_vacia() or self.ultimo is None or self.ultimo.siguiente is None:
            return []
        procesos_ordenados = []
        actual = self.ultimo.siguiente
        if actual is None:
            return []
        while True:
            procesos_ordenados.append(actual)
            actual = actual.siguiente
            if actual is None or actual == self.ultimo.siguiente:
                break
        return procesos_ordenados

# Variables globales para la simulación
cola_rr = ListaCircular()
cola_fcfs = collections.deque()
cola_pq = []
procesos_por_llegar = []
cola_bloqueados = []
proceso_actual_en_cpu = None
simulacion_activa = False
simulacion_pausada = False
hilo_simulacion = None
cpu_tiempo_actual = 0.0
quantum_value = 2.0
aging_time_x = 10.0
procesos_por_llegar_lock = threading.Lock()

# --- NUEVA INTERFAZ MODERNA ---

class ModernSimulatorUI:
    def _init_(self, root):
        self.root = root
        self.root.title("Simulador Multicolas Moderno")
        self.root.geometry("1200x700")
        self.root.configure(bg="#eaf1fb")
        self._setup_style()
        # --- Scroll principal (vertical y horizontal) ---
        self.outer_canvas = tk.Canvas(self.root, bg="#eaf1fb", highlightthickness=0)
        self.outer_canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar_y = ttk.Scrollbar(self.root, orient="vertical", command=self.outer_canvas.yview)
        self.scrollbar_y.pack(side="right", fill="y")
        self.scrollbar_x = ttk.Scrollbar(self.root, orient="horizontal", command=self.outer_canvas.xview)
        self.scrollbar_x = ttk.Scrollbar(self.root, orient="horizontal", command=self.outer_canvas.xview)
        self.scrollbar_x.pack(side="bottom", fill="x")
        self.outer_canvas.configure(yscrollcommand=self.scrollbar_y.set, xscrollcommand=self.scrollbar_x.set)
        self.scrollable_frame = tk.Frame(self.outer_canvas, bg="#eaf1fb")
        self.outer_canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.scrollable_frame.bind("<Configure>", lambda e: self.outer_canvas.configure(scrollregion=self.outer_canvas.bbox("all")))
        self._build_layout()
        self._actualizar_tabla_procesos()
        self._actualizar_tablas_colas()
        self._actualizar_consola()
        self._init_gantt_vars()
        self._actualizar_gantt([])
        self._actualizar_resultados([])

    def _setup_style(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TFrame", background="#eaf1fb")
        style.configure("TLabel", background="#eaf1fb", font=("Segoe UI", 10))
        style.configure("TButton", font=("Segoe UI", 10, "bold"), padding=6)
        style.configure("Treeview.Heading", font=("Segoe UI", 10, "bold"), background="#e0e7ef", foreground="#222")
        style.configure("Treeview", font=("Segoe UI", 10), rowheight=28, background="white", fieldbackground="white", foreground="#222")
        style.map("TButton", background=[('active', '#4fa3e3')])

    def _build_layout(self):
        # --- Barra superior ---
        topbar = tk.Frame(self.scrollable_frame, bg="#dbeafe", height=60)
        topbar.pack(side=tk.TOP, fill=tk.X)
        tk.Label(topbar, text="Simulador de Planificación Multicolas", font=("Segoe UI", 18, "bold"), bg="#dbeafe").pack(side=tk.LEFT, padx=30, pady=10)
        controls = tk.Frame(topbar, bg="#dbeafe")
        controls.pack(side=tk.RIGHT, padx=20)
        self.semaforo_canvas = tk.Canvas(controls, width=32, height=32, bg="#dbeafe", highlightthickness=0)
        self.semaforo_canvas.pack(side=tk.LEFT, padx=10)
        self._draw_semaforo_cpu(False)
        tk.Label(controls, text="Quantum:", bg="#dbeafe").pack(side=tk.LEFT, padx=2)
        self.entry_quantum = ttk.Entry(controls, width=6)
        self.entry_quantum.insert(0, "2.0")
        self.entry_quantum.pack(side=tk.LEFT, padx=2)
        tk.Label(controls, text="Envejecimiento:", bg="#dbeafe").pack(side=tk.LEFT, padx=2)
        self.entry_aging = ttk.Entry(controls, width=6)
        self.entry_aging.insert(0, "10.0")
        self.entry_aging.pack(side=tk.LEFT, padx=2)
        self.btn_iniciar = ttk.Button(controls, text="Iniciar", width=10, command=self._iniciar_simulacion)
        self.btn_iniciar.pack(side=tk.LEFT, padx=4)
        self.btn_pausar = ttk.Button(controls, text="Pausar", width=10, command=self._pausar_reanudar_simulacion, state=tk.DISABLED)
        self.btn_pausar.pack(side=tk.LEFT, padx=4)
        self.btn_reiniciar = ttk.Button(controls, text="Reiniciar", width=10, command=self._reiniciar_simulacion)
        self.btn_reiniciar.pack(side=tk.LEFT, padx=4)

        # --- Gestión de procesos: fila horizontal ---
        proc_row = tk.Frame(self.scrollable_frame, bg="#eaf1fb")
        proc_row.pack(fill=tk.X, padx=20, pady=(10, 2))
        # Formulario a la izquierda
        form = tk.Frame(proc_row, bg="white", bd=0, highlightbackground="#cbd5e1", highlightthickness=1)
        form.pack(side=tk.LEFT, padx=(0, 10), pady=2)
        tk.Label(form, text="Gestión de Procesos", font=("Segoe UI", 13, "bold"), bg="white").grid(row=0, column=0, columnspan=11, sticky="w", padx=10, pady=(8,0))
        tk.Label(form, text="ID:", bg="white").grid(row=1, column=0, padx=2, pady=2)
        self.entry_pid = ttk.Entry(form, width=7)
        self.entry_pid.grid(row=1, column=1, padx=2, pady=2)
        tk.Label(form, text="Llegada:", bg="white").grid(row=1, column=2, padx=2, pady=2)
        self.entry_at = ttk.Entry(form, width=7)
        self.entry_at.grid(row=1, column=3, padx=2, pady=2)
        tk.Label(form, text="Ráfaga:", bg="white").grid(row=1, column=4, padx=2, pady=2)
        self.entry_bt = ttk.Entry(form, width=7)
        self.entry_bt.grid(row=1, column=5, padx=2, pady=2)
        tk.Label(form, text="Cola:", bg="white").grid(row=1, column=6, padx=2, pady=2)
        self.combo_queue_type = ttk.Combobox(form, values=["RR", "FCFS", "PQ"], state="readonly", width=6)
        self.combo_queue_type.set("RR")
        self.combo_queue_type.grid(row=1, column=7, padx=2, pady=2)
        tk.Label(form, text="Prioridad:", bg="white").grid(row=1, column=8, padx=2, pady=2)
        self.entry_priority = ttk.Entry(form, width=7)
        self.entry_priority.grid(row=1, column=9, padx=2, pady=2)
        ttk.Button(form, text="Agregar", command=self._agregar_proceso, style="Accent.TButton").grid(row=1, column=10, padx=8)
        # Tabla a la derecha
        proc_table_frame = tk.Frame(proc_row, bg="white", bd=0, highlightbackground="#cbd5e1", highlightthickness=1)
        proc_table_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.tree_procesos = ttk.Treeview(proc_table_frame, columns=("ID", "Llegada", "Ráfaga", "Cola", "Prioridad"), show="headings", height=4)
        for col, w in zip(("ID", "Llegada", "Ráfaga", "Cola", "Prioridad"), (60, 80, 80, 80, 80)):
            self.tree_procesos.heading(col, text=col)
            self.tree_procesos.column(col, width=w, anchor="center")
        self.tree_procesos.pack(side=tk.LEFT, fill=tk.X, padx=10, pady=8)
        ttk.Button(proc_table_frame, text="Eliminar seleccionado", command=self._eliminar_proceso).pack(side=tk.LEFT, padx=8, pady=8)

        # --- Colas: fila horizontal ---
        colas_row = tk.Frame(self.scrollable_frame, bg="#eaf1fb")
        colas_row.pack(fill=tk.X, padx=20, pady=2)
        for nombre, tree_attr, color, label in [
            ("RR", "tree_rr", "#e0f2fe", "Cola Round Robin (Prioridad 1)"),
            ("FCFS", "tree_fcfs", "#f0fdf4", "Cola FCFS (Prioridad 2)"),
            ("PQ", "tree_pq", "#fef9c3", "Cola de Prioridades (Prioridad 3)")
        ]:
            card = tk.Frame(colas_row, bg=color, bd=0, highlightbackground="#cbd5e1", highlightthickness=1)
            card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=6)
            tk.Label(card, text=label, font=("Segoe UI", 11, "bold"), bg=color).pack(anchor="w", padx=10, pady=(8,0))
            tree = ttk.Treeview(card, columns=("ID", "Llegada", "Ráfaga") if nombre!="PQ" else ("ID", "Llegada", "Ráfaga", "Prioridad"), show="headings", height=3)
            for col in tree['columns']:
                tree.heading(col, text=col)
                tree.column(col, width=70, anchor="center")
            tree.pack(fill=tk.X, padx=10, pady=(2, 10))
            setattr(self, tree_attr, tree)

        # --- Gantt (debajo de colas, altura fija, con scroll propio) ---
        card_gantt = tk.Frame(self.scrollable_frame, bg="white", bd=0, highlightbackground="#cbd5e1", highlightthickness=1)
        card_gantt.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(card_gantt, text="Gráfico de Gantt", font=("Segoe UI", 11, "bold"), bg="white").pack(anchor="w", padx=10, pady=(8,0))
        gantt_frame = tk.Frame(card_gantt, bg="white")
        gantt_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(2, 10))
        # Scrollbars para el Gantt
        self.gantt_scroll_y = ttk.Scrollbar(gantt_frame, orient="vertical")
        self.gantt_scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.gantt_scroll_x = ttk.Scrollbar(gantt_frame, orient="horizontal")
        self.gantt_scroll_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.gantt_canvas = tk.Canvas(gantt_frame, bg="#f8fafc", height=220, width=1100, highlightthickness=0,
                                      yscrollcommand=self.gantt_scroll_y.set, xscrollcommand=self.gantt_scroll_x.set)
        self.gantt_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.gantt_scroll_y.config(command=self.gantt_canvas.yview)
        self.gantt_scroll_x.config(command=self.gantt_canvas.xview)

        # --- Resultados (debajo del Gantt, altura fija) ---
        card_res = tk.Frame(self.scrollable_frame, bg="white", bd=0, highlightbackground="#cbd5e1", highlightthickness=1)
        card_res.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(card_res, text="Resultados de Ejecución", font=("Segoe UI", 11, "bold"), bg="white").pack(anchor="w", padx=10, pady=(8,0))
        self.tree_resultados = ttk.Treeview(card_res, columns=("ID", "AT", "BT", "Cola", "Inicio", "Fin", "Duración", "Espera"), show="headings", height=4)
        for col, w in zip(("ID", "AT", "BT", "Cola", "Inicio", "Fin", "Duración", "Espera"), (60, 60, 60, 70, 70, 70, 80, 80)):
            self.tree_resultados.heading(col, text=col)
            self.tree_resultados.column(col, width=w, anchor="center")
        self.tree_resultados.pack(fill=tk.X, padx=10, pady=(2, 10))
        self.label_promedios = tk.Label(card_res, text="Promedio TAT: N/A | Promedio WT: N/A", font=("Segoe UI", 11, "bold"), bg="white")
        self.label_promedios.pack(pady=(0,8), padx=10, anchor="w")

        # --- Consola (parte inferior, altura fija) ---
        card_console = tk.Frame(self.scrollable_frame, bg="#1e293b", bd=0, highlightbackground="#cbd5e1", highlightthickness=1)
        card_console.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(card_console, text="Consola del Simulador", font=("Segoe UI", 11, "bold"), bg="#1e293b", fg="#bae6fd").pack(anchor="w", padx=10, pady=(8,0))
        self.text_consola = tk.Text(card_console, height=4, bg="#0f172a", fg="#00FF00", font=("Consolas", 10), state='disabled', relief="flat")
        self.text_consola.pack(fill=tk.X, expand=False, padx=10, pady=(2, 10))

    def _draw_semaforo_cpu(self, ocupado):
        self.semaforo_canvas.delete("all")
        color = "#e74c3c" if ocupado else "#2ecc71"
        self.semaforo_canvas.create_oval(6, 6, 26, 26, fill=color, outline="#888", width=2)

    def _agregar_proceso(self):
        pid = self.entry_pid.get().strip()
        at = self.entry_at.get().strip()
        bt = self.entry_bt.get().strip()
        queue_type = self.combo_queue_type.get()
        priority = self.entry_priority.get().strip()
        if not pid or not at or not bt:
            messagebox.showerror("Error", "Todos los campos son obligatorios (excepto prioridad si no es PQ).")
            return
        try:
            at = int(at)
            bt = float(bt)
            if at < 0 or bt <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Error", "Llegada debe ser entero >=0 y ráfaga >0.")
            return
        if any(p.id == pid for p in master_procesos):
            messagebox.showerror("Error", f"El ID '{pid}' ya existe.")
            return
        if queue_type == "PQ":
            try:
                priority = int(priority)
            except ValueError:
                messagebox.showerror("Error", "Prioridad debe ser un entero para PQ.")
                return
        else:
            priority = None
        nuevo = Proceso(pid, at, bt, priority, queue_type)
        master_procesos.append(nuevo)
        self.entry_pid.delete(0, tk.END)
        self.entry_at.delete(0, tk.END)
        self.entry_bt.delete(0, tk.END)
        self.entry_priority.delete(0, tk.END)
        # Permitir agregar durante simulación
        global simulacion_activa, cpu_tiempo_actual
        if simulacion_activa:
            with procesos_por_llegar_lock:
                # Si el AT es menor o igual al tiempo actual, encolar ya
                if at <= cpu_tiempo_actual:
                    nuevo.entry_time_to_queue = cpu_tiempo_actual
                    if queue_type == "RR":
                        cola_rr.encolar_proceso(nuevo)
                    elif queue_type == "FCFS":
                        cola_fcfs.append(nuevo)
                    elif queue_type == "PQ":
                        cola_pq.append(nuevo)
                        cola_pq.sort(key=lambda p: p.priority)
                    self._actualizar_consola(f"[Sistema] Proceso {pid} ({queue_type}) agregado en tiempo real y va a Listos (AT: {at}).")
                else:
                    procesos_por_llegar.append(nuevo)
                    procesos_por_llegar.sort(key=lambda p: p.t_llegada)
                    self._actualizar_consola(f"[Sistema] Proceso {pid} ({queue_type}) registrado para llegada futura (AT: {at}).")
            self._actualizar_tabla_procesos()
            self._actualizar_tablas_colas()
        else:
            with procesos_por_llegar_lock:
                procesos_por_llegar.append(nuevo)
                procesos_por_llegar.sort(key=lambda p: p.t_llegada)
            self._actualizar_tabla_procesos()
            self._actualizar_tablas_colas()

    def _eliminar_proceso(self):
        sel = self.tree_procesos.selection()
        if not sel:
            messagebox.showinfo("Selecciona", "Selecciona un proceso para eliminar.")
            return
        pid = self.tree_procesos.item(sel[0], 'values')[0]
        for i, p in enumerate(master_procesos):
            if p.id == pid:
                del master_procesos[i]
                break
        self._actualizar_tabla_procesos()

    def _actualizar_tabla_procesos(self):
        for item in self.tree_procesos.get_children():
            self.tree_procesos.delete(item)
        for p in master_procesos:
            self.tree_procesos.insert("", "end", values=(p.id, p.t_llegada, p.bt, p.queue_type, p.priority if p.priority is not None else ""))
        self._actualizar_tablas_colas()

    def _actualizar_tablas_colas(self):
        # RR
        for item in self.tree_rr.get_children():
            self.tree_rr.delete(item)
        for p in cola_rr.obtener_procesos_en_orden():
            self.tree_rr.insert("", "end", values=(p.id, p.t_llegada, p.bt))
        # FCFS
        for item in self.tree_fcfs.get_children():
            self.tree_fcfs.delete(item)
        for p in cola_fcfs:
            self.tree_fcfs.insert("", "end", values=(p.id, p.t_llegada, p.bt))
        # PQ
        for item in self.tree_pq.get_children():
            self.tree_pq.delete(item)
        for p in sorted(cola_pq, key=lambda p: p.priority if p.priority is not None else 999):
            self.tree_pq.insert("", "end", values=(p.id, p.t_llegada, p.bt, p.priority if p.priority is not None else ""))

    def _actualizar_consola(self, msg=None):
        self.text_consola.config(state='normal')
        if msg:
            self.text_consola.insert(tk.END, msg + "\n")
            self.text_consola.see(tk.END)
        self.text_consola.config(state='disabled')

    def _iniciar_simulacion(self):
        global simulacion_activa, simulacion_pausada, hilo_simulacion, quantum_value, aging_time_x
        # Leer quantum y envejecimiento de la UI
        try:
            quantum_value = float(self.entry_quantum.get())
            if quantum_value <= 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Error", "El quantum debe ser un número positivo.")
            return
        try:
            aging_time_x = float(self.entry_aging.get())
            if aging_time_x < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Error", "El envejecimiento debe ser un número positivo o cero.")
            return
        if not master_procesos:
            messagebox.showwarning("Sin Procesos", "Agrega al menos un proceso para iniciar la simulación.")
            return
        simulacion_activa = True
        simulacion_pausada = False
        self.btn_iniciar.config(state=tk.DISABLED)
        self.btn_pausar.config(state=tk.NORMAL, text="Pausar")
        self._actualizar_consola("[Sistema] Simulación iniciada.")
        hilo_simulacion = threading.Thread(target=self._ejecutar_simulacion, daemon=True)
        hilo_simulacion.start()

    def _pausar_reanudar_simulacion(self):
        global simulacion_pausada
        if not simulacion_activa:
            return
        simulacion_pausada = not simulacion_pausada
        if simulacion_pausada:
            self.btn_pausar.config(text="Reanudar")
            self._actualizar_consola("[Sistema] Simulación PAUSADA.")
        else:
            self.btn_pausar.config(text="Pausar")
            self._actualizar_consola("[Sistema] Simulación REANUDADA.")

    def _reiniciar_simulacion(self):
        global simulacion_activa, simulacion_pausada, hilo_simulacion
        simulacion_activa = False
        simulacion_pausada = False
        if hilo_simulacion and hilo_simulacion.is_alive():
            time.sleep(0.2)
        master_procesos.clear()
        cola_rr._init_()
        cola_fcfs.clear()
        cola_pq.clear()
        with procesos_por_llegar_lock:
            procesos_por_llegar.clear()
        cola_bloqueados.clear()
        self._actualizar_tabla_procesos()
        self._actualizar_tablas_colas()
        self._actualizar_consola("[Sistema] Simulador reiniciado.")
        self.btn_iniciar.config(state=tk.NORMAL)
        self.btn_pausar.config(state=tk.DISABLED, text="Pausar")

    def _init_gantt_vars(self):
        self.gantt_colors = ["#4fa3e3", "#2ecc71", "#f39c12", "#e74c3c", "#9b59b6", "#16a085", "#34495e", "#d35400"]
        random.shuffle(self.gantt_colors)
        self.gantt_y_map = {}
        self.gantt_next_y = 0

    def _actualizar_gantt(self, fragmentos):
        self.gantt_canvas.delete("all")
        PX_POR_UNIDAD = 30
        BAR_HEIGHT = 28
        START_Y = 40
        self.gantt_y_map = {}
        self.gantt_next_y = 0
        # Etiquetas de procesos
        for frag in fragmentos:
            pid = frag['original_id']
            if pid not in self.gantt_y_map:
                self.gantt_y_map[pid] = self.gantt_next_y
                self.gantt_next_y += 1
                y = START_Y + (self.gantt_y_map[pid] * (BAR_HEIGHT + 10))
                self.gantt_canvas.create_text(10, y + BAR_HEIGHT/2, text=f"P{pid}", anchor="w", font=("Segoe UI", 10, "bold"), fill="#34495e")
        # Barras de fragmentos
        for i, frag in enumerate(fragmentos):
            pid = frag['original_id']
            y = START_Y + (self.gantt_y_map[pid] * (BAR_HEIGHT + 10))
            x0 = frag['start_time'] * PX_POR_UNIDAD + 60
            x1 = frag['t_final'] * PX_POR_UNIDAD + 60
            color = self.gantt_colors[self.gantt_y_map[pid] % len(self.gantt_colors)]
            self.gantt_canvas.create_rectangle(x0, y, x1, y + BAR_HEIGHT, fill=color, outline="#222", width=2)
            self.gantt_canvas.create_text((x0 + x1) / 2, y + BAR_HEIGHT/2, text=frag['fragment_id'], font=("Segoe UI", 10, "bold"), fill="#fff")
        # Eje de tiempo
        max_time = max([frag['t_final'] for frag in fragmentos], default=10)
        for t in range(0, int(max_time) + 2):
            x = t * PX_POR_UNIDAD + 60
            self.gantt_canvas.create_line(x, 20, x, self.gantt_canvas.winfo_height(), fill="#bbb", dash=(2,2))
            self.gantt_canvas.create_text(x, 25, text=str(t), font=("Segoe UI", 9), fill="#888")
        self.gantt_canvas.configure(scrollregion=self.gantt_canvas.bbox("all"))

    def _actualizar_resultados(self, fragmentos):
        for item in self.tree_resultados.get_children():
            self.tree_resultados.delete(item)
        total_tat, total_wt, n = 0.0, 0.0, 0
        for frag in fragmentos:
            t_retorno = frag['t_final'] - frag['t_llegada']
            t_espera = t_retorno - frag['duration']
            self.tree_resultados.insert("", "end", values=(frag['fragment_id'], frag['t_llegada'], frag['bt'], frag['queue_type'], f"{frag['start_time']:.1f}", f"{frag['t_final']:.1f}", f"{t_retorno:.1f}", f"{t_espera:.1f}"))
            total_tat += t_retorno
            total_wt += t_espera
            n += 1
        if n:
            self.label_promedios.config(text=f"Promedio TAT: {total_tat/n:.2f} | Promedio WT: {total_wt/n:.2f}")
        else:
            self.label_promedios.config(text="Promedio TAT: N/A | Promedio WT: N/A")

    def _ejecutar_simulacion(self):
        global simulacion_activa, simulacion_pausada, proceso_actual_en_cpu, quantum_value, aging_time_x
        with procesos_por_llegar_lock:
            procesos_por_llegar[:] = []
            for p in master_procesos:
                p_copia = Proceso(p.id, p.t_llegada, p.bt, p.priority, p.queue_type)
                procesos_por_llegar.append(p_copia)
            procesos_por_llegar.sort(key=lambda p: p.t_llegada)
        cola_rr._init_()
        cola_fcfs.clear()
        cola_pq.clear()
        cola_bloqueados.clear()
        cpu_tiempo = 0.0
        fragmentos = []
        procesos_ejecutados_completos = []
        gantt_y_map = {}
        next_gantt_y = 0
        proceso_actual_en_cpu = None
        bloqueo_solicitado = False
        idx_color = 0
        fragment_count_map = {}
        # --- Simulación principal ---
        while (procesos_por_llegar or not cola_rr.esta_vacia() or cola_fcfs or cola_pq or proceso_actual_en_cpu or cola_bloqueados) and simulacion_activa:
            while simulacion_pausada and simulacion_activa:
                time.sleep(0.1)
                self.root.update_idletasks()
            if not simulacion_activa:
                break
            with procesos_por_llegar_lock:
                for p_arrival in list(procesos_por_llegar):
                    if p_arrival.t_llegada <= cpu_tiempo:
                        p_arrival.entry_time_to_queue = cpu_tiempo
                        if p_arrival.queue_type == "RR":
                            cola_rr.encolar_proceso(p_arrival)
                        elif p_arrival.queue_type == "FCFS":
                            cola_fcfs.append(p_arrival)
                        elif p_arrival.queue_type == "PQ":
                            cola_pq.append(p_arrival)
                            cola_pq.sort(key=lambda p: p.priority)
                        procesos_por_llegar.remove(p_arrival)
                        self._actualizar_consola(f"[Sistema] Proceso {p_arrival.id} ({p_arrival.queue_type}) llegó o fue desbloqueado.")
                procesos_por_llegar.sort(key=lambda p: p.t_llegada)
            if aging_time_x is not None and aging_time_x > 0:
                for p in list(cola_pq):
                    if hasattr(p, 'entry_time_to_queue') and cpu_tiempo - p.entry_time_to_queue >= aging_time_x:
                        cola_pq.remove(p)
                        p.queue_type = "FCFS"
                        p.entry_time_to_queue = cpu_tiempo
                        cola_fcfs.append(p)
                        self._actualizar_consola(f"[Envejecimiento] {p.id} PQ->FCFS")
                for p in list(cola_fcfs):
                    if hasattr(p, 'entry_time_to_queue') and cpu_tiempo - p.entry_time_to_queue >= aging_time_x:
                        cola_fcfs.remove(p)
                        p.queue_type = "RR"
                        p.entry_time_to_queue = cpu_tiempo
                        cola_rr.encolar_proceso(p)
                        self._actualizar_consola(f"[Envejecimiento] {p.id} FCFS->RR")
            self._actualizar_tablas_colas()
            if not cola_rr.esta_vacia():
                p = cola_rr.desencolar_proceso_rr()
            elif cola_fcfs:
                p = cola_fcfs.popleft()
            elif cola_pq:
                cola_pq.sort(key=lambda p: p.priority)
                p = cola_pq.pop(0)
            else:
                p = None
            if p:
                proceso_actual_en_cpu = p
                self._draw_semaforo_cpu(True)
                t_espera = max(0.0, cpu_tiempo - getattr(p, 't_llegada', 0))
                if not hasattr(p, 't_arranque') or p.t_arranque == -1:
                    p.t_arranque = cpu_tiempo
                run_time_for_slice = p.bt
                if p.queue_type == "RR":
                    run_time_for_slice = min(p.bt, quantum_value)
                start_of_current_execution = cpu_tiempo
                ejecutado_rafaga_actual = 0.0
                # Fragmentación y ejecución animada
                while ejecutado_rafaga_actual < run_time_for_slice - 1e-9 and simulacion_activa:
                    while simulacion_pausada and simulacion_activa:
                        time.sleep(0.1)
                        self.root.update_idletasks()
                    if not simulacion_activa:
                        break
                    with procesos_por_llegar_lock:
                        for p_arrival_check in list(procesos_por_llegar):
                            if p_arrival_check.t_llegada <= cpu_tiempo:
                                p_arrival_check.entry_time_to_queue = cpu_tiempo
                                if p_arrival_check.queue_type == "RR":
                                    cola_rr.encolar_proceso(p_arrival_check)
                                elif p_arrival_check.queue_type == "FCFS":
                                    cola_fcfs.append(p_arrival_check)
                                elif p_arrival_check.queue_type == "PQ":
                                    cola_pq.append(p_arrival_check)
                                    cola_pq.sort(key=lambda pc: pc.priority)
                                procesos_por_llegar.remove(p_arrival_check)
                                self._actualizar_consola(f"[Sistema] Proceso {p_arrival_check.id} llegó y va a Listos.")
                        procesos_por_llegar.sort(key=lambda p_sort: p_sort.t_llegada)
                    current_queue_priority = {"RR": 1, "FCFS": 2, "PQ": 3}[p.queue_type]
                    if (not cola_rr.esta_vacia() and current_queue_priority > 1) or \
                       (cola_fcfs and current_queue_priority > 2) or \
                       (cola_pq and current_queue_priority > 3 and cola_pq[0].priority < getattr(p, 'priority', 999)):
                        break
                    step = min(0.1, run_time_for_slice - ejecutado_rafaga_actual)
                    time.sleep(step)
                    cpu_tiempo += step
                    ejecutado_rafaga_actual += step
                    # Actualizar fragmento parcial en Gantt
                    if p.id not in fragment_count_map:
                        fragment_count_map[p.id] = 1
                    frag_id = f"{p.id}-{fragment_count_map[p.id]}"
                    frag = {
                        'fragment_id': frag_id,
                        'original_id': p.id,
                        't_llegada': getattr(p, 'original_at', 0),
                        'bt': getattr(p, 'original_bt', 0),
                        'start_time': start_of_current_execution,
                        't_final': cpu_tiempo,
                        'duration': ejecutado_rafaga_actual,
                        'wait_time_before_fragment': t_espera,
                        'is_completed': False,
                        'queue_type': p.queue_type
                    }
                    # Reemplazar o agregar el fragmento parcial
                    fragmentos = [f for f in fragmentos if f['fragment_id'] != frag_id] + [frag]
                    self._actualizar_gantt(fragmentos)
                    self._actualizar_resultados(fragmentos)
                # Fragmento final
                p.bt -= ejecutado_rafaga_actual
                if p.id not in fragment_count_map:
                    fragment_count_map[p.id] = 1
                else:
                    fragment_count_map[p.id] += 1
                frag_id = f"{p.id}-{fragment_count_map[p.id]}"
                frag = {
                    'fragment_id': frag_id,
                    'original_id': p.id,
                    't_llegada': getattr(p, 'original_at', 0),
                    'bt': getattr(p, 'original_bt', 0),
                    'start_time': start_of_current_execution,
                    't_final': cpu_tiempo,
                    'duration': ejecutado_rafaga_actual,
                    'wait_time_before_fragment': t_espera,
                    'is_completed': p.bt <= 1e-9,
                    'queue_type': p.queue_type
                }
                fragmentos = [f for f in fragmentos if f['fragment_id'] != frag_id] + [frag]
                self._actualizar_gantt(fragmentos)
                self._actualizar_resultados(fragmentos)
                self._actualizar_tablas_colas()
                if p.bt <= 1e-9:
                    t_final = cpu_tiempo
                    turnaround = t_final - getattr(p, 'original_at', 0)
                    waiting = turnaround - getattr(p, 'original_bt', 0)
                    procesos_ejecutados_completos.append({
                        'id': p.id, 't_llegada': getattr(p, 'original_at', 0), 'bt': getattr(p, 'original_bt', 0),
                        'start_time': getattr(p, 't_arranque', 0), 't_final': t_final,
                        't_espera': turnaround, 'waiting_time': waiting
                    })
                    self._actualizar_consola(f"[CPU] {p.id} ({p.queue_type}) TERMINÓ en t={t_final:.1f}")
                    proceso_actual_en_cpu = None
                    self._draw_semaforo_cpu(False)
                else:
                    p.t_llegada = cpu_tiempo
                    p.entry_time_to_queue = cpu_tiempo
                    if p.queue_type == "RR":
                        cola_rr.encolar_proceso(p)
                    elif p.queue_type == "FCFS":
                        cola_fcfs.append(p)
                    elif p.queue_type == "PQ":
                        cola_pq.append(p)
                        cola_pq.sort(key=lambda proc: proc.priority)
                    self._actualizar_consola(f"[CPU] {p.id} ({p.queue_type}) fue PREEMPTADO y reencolado (restan {p.bt:.1f}u).")
                    proceso_actual_en_cpu = None
                    self._draw_semaforo_cpu(False)
            else:
                self._draw_semaforo_cpu(False)
                time.sleep(0.1)
                cpu_tiempo += 0.1
        simulacion_activa = False
        self.btn_iniciar.config(state=tk.NORMAL)
        self.btn_pausar.config(state=tk.DISABLED, text="Pausar")
        self._actualizar_consola("[Sistema] Simulación finalizada.")

if _name_ == "_main_":
    root = tk.Tk()
    app = ModernSimulatorUI(root)
    root.mainloop()
