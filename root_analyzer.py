import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from PIL import Image, ImageTk, ImageEnhance, ImageDraw
import numpy as np
import math
import os
import csv
import json
import re

# Add these constants near the top of the file
PAPER_SIZES = {
    'A3': 297,  # mm
    'A4': 210,  # mm
    'Custom': 0,  # placeholder for custom size
    'Output pixels': None  # output raw pixel counts
}

class RootAnalyzer(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Root System Analyzer")
        self.geometry("1200x800")
        
        self.current_image = None
        self.photo_image = None
        self.current_plant = None
        self.selected_plant = None
        self.selected_curve = None  # Add this to track selected curve
        self.plants = {}  # Store all plant data
        self.current_curve_points = []  # Store current curve points
        self.drawing_state = None  # Control drawing state
        self.points_history = []  # Store point addition history
        self.redo_history = []   # Store redo history
        self.last_added_point = None  # Store last added point
        self.dragging_point = None  # Store currently dragging point
        self.dragging_point_index = None  # Store dragging point index
        
        # Define fixed colors for plants
        self.fixed_plant_colors = {
            1: '#FF0000',  # Red for plant 1
            2: '#800080',  # Purple for plant 2
            3: '#0000FF',  # Blue
            4: '#008000',  # Green
            5: '#FFA500',  # Orange
            6: '#00FFFF',  # Cyan
            7: '#FF00FF',  # Magenta
            8: '#008080',  # Teal
            9: '#FFD700',  # Gold
            10: '#4B0082', # Indigo
            # Add more colors if needed
        }
        
        self.stem_color = '#006400'  # Dark Green for stems
        self.current_type = 'root'  # 'root' or 'stem'
        self.show_background = True  
        self.current_image_name = None  
        self.current_image_path = None  
        self.current_image_dir = None   # Add this line to store the directory of current image
        
        
        self.current_csv_file = None  
        
        self.import_line_start_ratio = 0.1  
        self.import_line_end_ratio = 0.9    
        self.import_line_height_ratio = 0.1  
        
        self.scale_factor = 1.0  
        
        self.current_paper_size = 'Output pixels'  # Default paper size
        self.custom_size = 297  # Default custom size in mm
        
        # Add these instance variables in the __init__ method
        self.original_image_width = 0  # Add this
        self.original_image_height = 0  # Add this
        
        self.display_zoom = 1.0  # Add zoom control
        self.base_scale = 1.0    # Add base scale for window fitting
        self.total_scale = 1.0   # Total scale (base_scale * display_zoom)
        
        self.original_image = None  # Add this line
        
        # Add these to __init__
        self.space_pressed = False
        self.last_pan_x = 0
        self.last_pan_y = 0
        
        self.setup_ui()
        
    def setup_ui(self):
        # Create main frame
        self.main_frame = ttk.Frame(self)
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Create a canvas and scrollbar for the toolbar
        toolbar_canvas = tk.Canvas(self.main_frame, width=200)
        toolbar_scrollbar = ttk.Scrollbar(self.main_frame, orient="vertical", command=toolbar_canvas.yview)
        
        # Left toolbar (now inside a frame that will be placed in the canvas)
        self.toolbar = ttk.Frame(toolbar_canvas)
        
        # Configure the canvas
        toolbar_canvas.configure(yscrollcommand=toolbar_scrollbar.set)
        
        # Pack the scrollbar and canvas
        toolbar_scrollbar.pack(side=tk.LEFT, fill=tk.Y)
        toolbar_canvas.pack(side=tk.LEFT, fill=tk.Y)
        
        # Create a window in the canvas to hold the toolbar
        toolbar_window = toolbar_canvas.create_window((0, 0), window=self.toolbar, anchor=tk.NW)
        
        # Add buttons and store them as instance variables
        self.open_button = ttk.Button(self.toolbar, text="Open Image", command=self.open_image)
        self.open_button.pack(fill=tk.X, pady=2)
        
        self.add_plant_button = ttk.Button(self.toolbar, text="Add Plant (Q)", command=self.add_plant)
        self.add_plant_button.pack(fill=tk.X, pady=2)
        
        self.add_root_button = ttk.Button(self.toolbar, text="Add Root (W)", 
                                        command=lambda: self.start_drawing('root'))
        self.add_root_button.pack(fill=tk.X, pady=2)
        
        self.add_stem_button = ttk.Button(self.toolbar, text="Add Stem (E)", 
                                          command=lambda: self.start_drawing('stem'))
        self.add_stem_button.pack(fill=tk.X, pady=2)
        
        # Add finish button (disabled by default)
        self.finish_button = ttk.Button(self.toolbar, text="Finish Drawing (S)", 
                                      command=self.finish_drawing, state='disabled')
        self.finish_button.pack(fill=tk.X, pady=2)
        
        # Remove save button from here
        
        # Plant list frame
        self.plant_frame = ttk.Frame(self.toolbar)
        self.plant_frame.pack(fill=tk.X, pady=2)
        
        # Add plant list label
        ttk.Label(self.plant_frame, text="Roots and Stemes").pack(fill=tk.X)
        
        # Create treeview for plants and roots
        self.tree = ttk.Treeview(self.plant_frame, height=15, selectmode='browse', columns=('delete',))
        self.tree.pack(fill=tk.X)
        self.tree.heading('#0', text='Plant/Root/Stem', anchor='w')
        self.tree.heading('delete', text='', anchor='w')  
        self.tree.column('delete', width=30, anchor='center')  
        
        # Bind tree click events
        self.tree.bind('<Button-1>', self.on_tree_click)
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        
        # Add style for tree items
        style = ttk.Style()
        style.configure("Root.Treeview.Item", foreground='white', background='black')
        style.configure("Stem.Treeview.Item", foreground='black', background='#2ECC71')
        
        # Add image processing controls
        self.add_image_controls()
        
        # Add scrollbar
        scrollbar = ttk.Scrollbar(self.plant_frame, orient="vertical", command=self.tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.configure(yscrollcommand=scrollbar.set)
        
        # Configure the canvas to update scroll region when toolbar size changes
        def configure_scroll_region(event):
            toolbar_canvas.configure(scrollregion=toolbar_canvas.bbox("all"))
        
        # Bind the configure event
        self.toolbar.bind('<Configure>', configure_scroll_region)
        
        # Make sure the canvas width stays fixed
        def on_canvas_configure(event):
            toolbar_canvas.itemconfig(toolbar_window, width=event.width)
        
        toolbar_canvas.bind('<Configure>', on_canvas_configure)
        
        # Right canvas frame
        self.canvas_frame = ttk.Frame(self.main_frame)
        self.canvas_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # Add image title label
        self.image_title = ttk.Label(self.canvas_frame, text="No image loaded", anchor="center")
        self.image_title.pack(fill=tk.X, pady=5)
        
        # Canvas
        self.canvas = tk.Canvas(self.canvas_frame, bg='white')
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        
        def on_mousewheel(event):
            # Check if Ctrl key is pressed (state = 4)
            if event.state & 0x4:
                if event.delta > 0:
                    self.zoom_in()
                else:
                    self.zoom_out()
            else:
                # Normal scrolling behavior when Ctrl is not pressed
                self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        
        # Bind mousewheel for zooming after canvas creation
        self.canvas.bind("<MouseWheel>", on_mousewheel)  # Windows
        self.canvas.bind("<Button-4>", lambda e: on_mousewheel(type('Event', (), {'state': 4, 'delta': 120})))  # Linux up
        self.canvas.bind("<Button-5>", lambda e: on_mousewheel(type('Event', (), {'state': 4, 'delta': -120})))  # Linux down
        
        # Add mouse event bindings
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        
        # Status bar
        self.status_var = tk.StringVar()
        self.status_bar = ttk.Label(self, textvariable=self.status_var)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Bind keyboard events
        self.bind('<Control-z>', self.undo_last_point)  
        self.bind('<Control-Z>', self.redo_last_point)  
        self.bind('<Control-s>', lambda e: self.save_all_data())  
        self.bind('<Left>', self.switch_to_previous_image)  
        self.bind('<Right>', self.switch_to_next_image)  
        
        # Add new keyboard shortcuts
        self.bind('q', self.handle_q_shortcut)
        self.bind('w', self.handle_w_shortcut)
        self.bind('e', self.handle_e_shortcut)
        self.bind('s', self.handle_s_shortcut)
        
        # Add bottom buttons frame
        bottom_buttons_frame = ttk.Frame(self.toolbar)
        bottom_buttons_frame.pack(fill=tk.X, pady=2, side=tk.BOTTOM)
        
        # Create style for colored buttons
        style = ttk.Style()
        style.configure("Green.TButton", foreground="dark green")
        style.configure("Red.TButton", foreground="red")
        
        # Add save and delete buttons side by side
        save_delete_frame = ttk.Frame(bottom_buttons_frame)
        save_delete_frame.pack(fill=tk.X, expand=True)
        
        self.save_button = ttk.Button(save_delete_frame, text="Save (Ctrl+S)", 
                                     command=self.save_all_data, style="Green.TButton")
        self.save_button.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 1))
        
        ttk.Button(save_delete_frame, text="Delete All", 
                   command=self.confirm_delete_all, style="Red.TButton").pack(
                       side=tk.LEFT, fill=tk.X, expand=True, padx=(1, 0))
        
        # Add zoom methods
        self.bind('-', self.zoom_out)
        self.bind('=', self.zoom_in)
        self.bind('+', self.zoom_in)  # For shift+=
        
        # Add these bindings
        self.canvas.bind("<Motion>", self.on_mouse_move)
        self.canvas.bind("<Button-2>", self.start_pan)  # Middle mouse button press
        self.canvas.bind("<B2-Motion>", self.on_pan_drag)  # Middle mouse button drag
        self.canvas.bind("<ButtonRelease-2>", self.end_pan)  # Middle mouse button release
        
        # Add Escape key binding
        self.bind('<Escape>', self.cancel_drawing)
        
    def add_image_controls(self):
        """Add image processing controls"""
        control_frame = ttk.LabelFrame(self.toolbar, text="Image Controls")
        control_frame.pack(fill=tk.X, pady=5)
        
        # Add zoom controls
        zoom_frame = ttk.Frame(control_frame)
        zoom_frame.pack(fill=tk.X, pady=2)
        
        ttk.Button(zoom_frame, text="-", width=3, command=self.zoom_out).pack(side=tk.LEFT, padx=2)
        ttk.Button(zoom_frame, text="+", width=3, command=self.zoom_in).pack(side=tk.LEFT, padx=2)
        ttk.Label(zoom_frame, text="Zoom").pack(side=tk.LEFT, padx=5)
        
        # Add paper size selection
        paper_frame = ttk.Frame(control_frame)
        paper_frame.pack(fill=tk.X, pady=2)
        
        ttk.Label(paper_frame, text="Paper Size:").pack(side=tk.LEFT, padx=2)
        self.paper_size_var = tk.StringVar(value=self.current_paper_size)
        paper_size_combo = ttk.Combobox(paper_frame, 
                                      textvariable=self.paper_size_var,
                                      values=list(PAPER_SIZES.keys()),
                                      width=10,
                                      state='readonly')
        paper_size_combo.pack(side=tk.LEFT, padx=2)
        paper_size_combo.bind('<<ComboboxSelected>>', self.on_paper_size_change)
        
        # Add custom size entry
        custom_frame = ttk.Frame(control_frame)
        custom_frame.pack(fill=tk.X, pady=2)
        
        ttk.Label(custom_frame, text="Custom Size (mm):").pack(side=tk.LEFT, padx=2)
        self.custom_size_var = tk.StringVar(value=str(self.custom_size))
        self.custom_size_entry = ttk.Entry(custom_frame, 
                                         textvariable=self.custom_size_var,
                                         width=8,
                                         state='disabled')
        self.custom_size_entry.pack(side=tk.LEFT, padx=2)
        self.custom_size_var.trace('w', self.on_custom_size_change)
        
        # Add existing controls
        # self.toggle_bg_button = ttk.Button(control_frame, text="Toggle Background",
        #                                  command=self.toggle_background)
        # self.toggle_bg_button.pack(fill=tk.X, pady=2)
        
        # Contrast control
        ttk.Label(control_frame, text="Contrast:").pack(fill=tk.X)
        self.contrast_scale = ttk.Scale(control_frame, from_=0.0, to=2.0, 
                                      orient=tk.HORIZONTAL, value=1.0,
                                      command=self.update_image)
        self.contrast_scale.pack(fill=tk.X)
        
        # Brightness control
        ttk.Label(control_frame, text="Brightness:").pack(fill=tk.X)
        self.brightness_scale = ttk.Scale(control_frame, from_=0.0, to=2.0,
                                        orient=tk.HORIZONTAL, value=1.0,
                                        command=self.update_image)
        self.brightness_scale.pack(fill=tk.X)
        
    def resize_image(self):
        if self.original_image:
            # Get original dimensions
            orig_width, orig_height = self.original_image_width, self.original_image_height
            
            # Get canvas size
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            
            # Calculate base scaling ratio
            self.base_scale = min(canvas_width/orig_width, canvas_height/orig_height)
            
            # Apply zoom factor
            self.total_scale = self.base_scale * self.display_zoom
            
            # Create resized version for display
            new_width = int(orig_width * self.total_scale)
            new_height = int(orig_height * self.total_scale)
            self.current_image = self.original_image.resize((new_width, new_height))
            
            # Apply current image adjustments
            contrast = float(self.contrast_scale.get())
            brightness = float(self.brightness_scale.get())
            enhanced = self.current_image.copy()
            enhanced = ImageEnhance.Contrast(enhanced).enhance(contrast)
            enhanced = ImageEnhance.Brightness(enhanced).enhance(brightness)
            
            # Add border to image
            bordered_image = self.add_border_to_image(enhanced)
            
            # Update displayed image
            self.photo_image = ImageTk.PhotoImage(bordered_image)
            self.canvas.delete("all")  # Clear canvas
            self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
            
            # Update canvas scroll region
            self.canvas.config(scrollregion=(0, 0, new_width, new_height))
            
            # Redraw all curves
            self.redraw_all_curves()
            
            # Maintain current view position
            if hasattr(self, 'last_view_x') and hasattr(self, 'last_view_y'):
                self.canvas.xview_moveto(self.last_view_x)
                self.canvas.yview_moveto(self.last_view_y)
            
            # Store current view position
            self.last_view_x = self.canvas.xview()[0]
            self.last_view_y = self.canvas.yview()[0]
            
            # After redrawing all curves
            if self.drawing_state:
                self.draw_temp_line()
                self.preview_curve()
                
    def add_border_to_image(self, image):
        """Add a visible border around the image"""
        width, height = image.size
        
        # Create a copy that preserves original mode (RGB or RGBA)
        bordered = image.copy()
        
        # Create a drawing object
        draw = ImageDraw.Draw(bordered)
        
        # Draw border (rectangle around the edges)
        border_color = (255, 0, 0)  # Red border
        border_width = 2
        
        # Draw four lines for the border
        # Top line
        draw.line([(0, 0), (width-1, 0)], fill=border_color, width=border_width)
        # Right line
        draw.line([(width-1, 0), (width-1, height-1)], fill=border_color, width=border_width)
        # Bottom line
        draw.line([(width-1, height-1), (0, height-1)], fill=border_color, width=border_width)
        # Left line
        draw.line([(0, height-1), (0, 0)], fill=border_color, width=border_width)
        
        return bordered
    
    def update_image(self, *args):
        if not self.current_image:
            return
            
        # Get current contrast and brightness values
        contrast = float(self.contrast_scale.get())
        brightness = float(self.brightness_scale.get())
        
        # Apply image adjustments
        enhanced = self.current_image.copy()
        enhanced = ImageEnhance.Contrast(enhanced).enhance(contrast)
        enhanced = ImageEnhance.Brightness(enhanced).enhance(brightness)
        
        # Add border to image
        bordered_image = self.add_border_to_image(enhanced)
        
        # Update display
        self.photo_image = ImageTk.PhotoImage(bordered_image)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
        self.redraw_all_curves()

    def open_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image files", "*.png *.jpg *.jpeg *.bmp *.gif")])
        if file_path:
            if self.current_image_name and self.plants:
                self.save_backup()
                self.save_current_csv()
                self.save_labeled_png()  # Save labeled PNG before switching
            
            self.current_image_path = file_path
            self.current_image_dir = os.path.dirname(file_path)  # Store the directory
            
            self.plants = {}
            self.plant_colors = {}
            self.color_index = 0
            self.current_curve_points = []
            self.points_history = []
            self.redo_history = []
            self.drawing_state = None
            self.current_type = None
            self.last_drawing_type = None
            self.current_plant = None
            
            self.tree.delete(*self.tree.get_children())
            
            self.canvas.delete("all")
            
            self.original_image = Image.open(file_path)  # Store original image
            self.original_image_width, self.original_image_height = self.original_image.size  # Store original dimensions
            self.current_image = self.original_image.copy()  # Working copy
            self.resize_image()  # This will create a resized version for display
            self.current_image_name = os.path.basename(file_path)
            
            self.image_title.config(text=self.current_image_name)
            
            base_name = os.path.splitext(self.current_image_name)[0]
            self.current_csv_file = os.path.join(self.current_image_dir, f"{base_name}.csv")
            
            # Try to load backup from the new location
            label_data_dir = os.path.join(self.current_image_dir, "label data")
            if os.path.exists(label_data_dir):
                backup_file = os.path.join(label_data_dir, f"{base_name}.json")
                if os.path.exists(backup_file):
                    self.load_backup()
                    self.restore_csv_from_backup()
            else:
                # Try the old location if the new one doesn't exist
                backup_file = os.path.join(self.current_image_dir, f"{self.current_image_name}.json")
                if os.path.exists(backup_file):
                    self.load_backup()
                    self.restore_csv_from_backup()
            
            contrast = float(self.contrast_scale.get())
            brightness = float(self.brightness_scale.get())
            
            enhanced = self.current_image.copy()
            enhanced = ImageEnhance.Contrast(enhanced).enhance(contrast)
            enhanced = ImageEnhance.Brightness(enhanced).enhance(brightness)
            
            # Add border to image
            bordered_image = self.add_border_to_image(enhanced)
            
            self.photo_image = ImageTk.PhotoImage(bordered_image)
            self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
            self.redraw_all_curves()

    def display_image(self):
        if self.current_image:
            self.photo_image = ImageTk.PhotoImage(self.current_image)
            self.canvas.delete("all")
            self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
            self.redraw_all_curves()
            
    def add_plant(self):
        """Create a new plant and initialize its data structure"""
        self.current_plant = len(self.plants) + 1
        self.plants[self.current_plant] = []  # Initialize empty plant entry
        self.update_tree_view()
        self.status_var.set(f"Started new plant {self.current_plant}")
        
    def get_plant_color(self, plant_id):
        """Get color for a plant based on its ID"""
        if plant_id in self.fixed_plant_colors:
            return self.fixed_plant_colors[plant_id]
        # Fallback color for plants beyond the predefined colors
        return f'#{hash(str(plant_id)) & 0xFFFFFF:06x}'  # Generate a color based on plant ID
        
    def start_drawing(self, type_name):
        """Start drawing a new root or stem"""
        if not self.current_plant:
            messagebox.showerror("Error", "Please select or add a plant first")
            return
            
        self.current_type = type_name
        self.drawing_state = "start"
        self.current_curve_points = []
        self.status_var.set(f"Select start point for {type_name}")
        
        # Only disable drawing-related buttons
        self.add_plant_button.configure(state='disabled')
        self.add_root_button.configure(state='disabled')
        self.add_stem_button.configure(state='disabled')
        self.save_button.configure(state='disabled')
        self.finish_button.configure(state='disabled')
        
        # Keep open button enabled
        self.open_button.configure(state='normal')   

    def on_tree_select(self, event):
        """Handle tree view selection"""
        selected_item = self.tree.selection()
        if selected_item:
            item = selected_item[0]
            parent = self.tree.parent(item)
            
            if parent:  # If it's a curve item
                plant_id = int(self.tree.item(parent, "text").split()[1])
                curve_idx = int(self.tree.item(item, "text").split()[1].strip(":")) - 1
                self.selected_plant = plant_id
                self.selected_curve = curve_idx
                self.current_plant = plant_id
            else:  # If it's a plant item
                plant_id = int(self.tree.item(item, "text").split()[1])
                self.selected_plant = plant_id
                self.selected_curve = None
                self.current_plant = plant_id
            
            self.redraw_all_curves()

    def highlight_selected_curve(self, item):
        """Highlight the selected curve by making it wider"""
        # First reset all curves to normal width
        self.redraw_all_curves()
        
        # Get plant and curve info from selected item
        parent = self.tree.parent(item)
        if parent:  # If it's a curve item
            plant_id = int(self.tree.item(parent, "text").split()[1])
            curve_idx = int(self.tree.item(item, "text").split()[1].strip(":")) - 1
            
            # Redraw the selected curve with wider width
            if 0 <= curve_idx < len(self.plants[plant_id]):
                color = self.get_plant_color(plant_id)
                curve = self.plants[plant_id][curve_idx]
                display_points = [(x * self.total_scale, y * self.total_scale) 
                                for x, y in curve['points']]
                
                # Draw thicker line for selected curve
                if len(display_points) >= 2:
                    self.draw_permanent_bezier(display_points, color, width=4)

    def find_nearest_point(self, x, y, max_distance=10):
        """Find the nearest point to the given coordinates within max_distance pixels"""
        try:
            if not self.current_curve_points:
                return None, None
                
            nearest_point = None
            nearest_index = None
            min_distance = float('inf')
            
            # Convert max_distance from screen to image coordinates
            max_distance = max_distance / self.total_scale
            
            for i, point in enumerate(self.current_curve_points):
                dx = point[0] - x
                dy = point[1] - y
                distance = math.sqrt(dx*dx + dy*dy)
                
                if distance < min_distance:
                    min_distance = distance
                    nearest_point = point
                    nearest_index = i
                    
            # Only return the point if it's within max_distance
            if min_distance <= max_distance:
                return nearest_point, nearest_index
            return None, None
            
        except Exception as e:
            print(f"Error in find_nearest_point: {str(e)}")
            return None, None

    def on_canvas_click(self, event):
        """Handle canvas click events"""
        try:
            print("\n=== on_canvas_click ===")
            print(f"Current drawing state: {self.drawing_state}")
            print(f"Current points before: {self.current_curve_points}")
            
            # Auto-start drawing if we just finished a root/stem
            if not self.drawing_state and hasattr(self, 'last_drawing_type') and self.last_drawing_type == 'root':
                self.start_drawing('root')
            
            if self.drawing_state:
                # Convert to canvas coordinates then to image coordinates
                canvas_x = self.canvas.canvasx(event.x)
                canvas_y = self.canvas.canvasy(event.y)
                
                # Convert to image coordinates
                x = canvas_x / self.total_scale
                y = canvas_y / self.total_scale
                
                print(f"Click at canvas: ({canvas_x}, {canvas_y}), image: ({x}, {y})")

                # Check if we need to auto-create a plant
                if not self.current_plant or self.current_plant not in self.plants:
                    self.add_plant()
                    
                if self.drawing_state == "start":
                    # Check if current plant already has roots
                    if self.plants[self.current_plant]:
                        # Use the start point of the first root
                        first_root = self.plants[self.current_plant][0]
                        first_point = first_root['points'][0]
                        x, y = first_point[0], first_point[1]
                        
                    self.current_curve_points = [(x, y)]
                    self.points_history.append(("start", (x, y)))
                    self.drawing_state = "end"
                    self.status_var.set("Select end point")
                    print(f"Start point added at ({x}, {y})")
                    print(f"Current points after start: {self.current_curve_points}")
                    self.redraw_current_curve()
                    self.draw_temp_line()
                    
                elif self.drawing_state == "end":
                    # Ensure minimum distance from start point
                    if len(self.current_curve_points) > 0:
                        start_point = self.current_curve_points[0]
                        dist = math.hypot(x - start_point[0], y - start_point[1])
                        if dist < 5 / self.total_scale:  # Minimum 5 pixels in screen space
                            print("End point too close to start point")
                            return
                        
                    self.current_curve_points.append((x, y))
                    self.points_history.append(("end", (x, y)))
                    self.drawing_state = "control"
                    self.status_var.set("Select middle points or click Finish")
                    self.finish_button.configure(state='normal')
                    print(f"End point added at ({x}, {y})")
                    print(f"Current points after end: {self.current_curve_points}")
                    self.redraw_current_curve()
                    self.draw_temp_line()
                    
                elif self.drawing_state == "control":
                    new_point = (x, y)
                    self.points_history.append(("control", new_point))
                    print(f"Adding control point at ({x}, {y})")
                    print(f"Current points before adding control: {self.current_curve_points}")
                    
                    # Add the point and get its index
                    insert_index = self.add_and_sort_point(new_point)
                    if insert_index is not None:  # If point was successfully added
                        # Set this new point as the dragging point
                        self.dragging_point = new_point
                        self.dragging_point_index = insert_index
                        print(f"New point added at index {insert_index} and set for dragging")
                    
                    print(f"Current points after adding control: {self.current_curve_points}")
                    self.redraw_current_curve()
                    self.draw_temp_line()
                    
        except Exception as e:
            print(f"Error in on_canvas_click: {str(e)}")
            print(f"Current state when error occurred: {self.drawing_state}")
            print(f"Current points when error occurred: {self.current_curve_points}")
            # Try to recover the drawing state
            if hasattr(self, 'current_curve_points'):
                if len(self.current_curve_points) >= 2:
                    self.drawing_state = "control"
                elif len(self.current_curve_points) == 1:
                    self.drawing_state = "end"
                else:
                    self.drawing_state = "start"
            self.status_var.set(f"Error occurred: {str(e)}")

    def add_and_sort_point(self, new_point):
        """Add and sort a new control point into the curve while preserving start and end points"""
        try:
            print("\n=== add_and_sort_point ===")
            print(f"Adding new point: {new_point}")
            print(f"Current points before: {self.current_curve_points}")
            
            if len(self.current_curve_points) < 2:
                print(f"Warning: Cannot add point, need at least 2 points. Current points: {len(self.current_curve_points)}")
                return None
                
            # Store start and end points
            start_point = self.current_curve_points[0]
            end_point = self.current_curve_points[-1]
            print(f"Start point: {start_point}")
            print(f"End point: {end_point}")
                
            # If this is the first middle point, insert it between start and end points
            if len(self.current_curve_points) == 2:
                # Check if the new point is too close to either end point
                start_dist = math.hypot(new_point[0] - start_point[0],
                                      new_point[1] - start_point[1])
                end_dist = math.hypot(new_point[0] - end_point[0],
                                    new_point[1] - end_point[1])
                min_dist = 5 / self.total_scale  # Minimum 5 pixels in screen space
                
                print(f"First middle point - distances: start={start_dist}, end={end_dist}, min={min_dist}")
                
                if start_dist < min_dist or end_dist < min_dist:
                    print(f"Point too close to endpoints: start_dist={start_dist}, end_dist={end_dist}")
                    return None
                    
                # Insert between start and end while preserving them
                self.current_curve_points = [start_point, new_point, end_point]
                print(f"Added first middle point between start and end. Total points: {len(self.current_curve_points)}")
                print(f"Current points after: {self.current_curve_points}")
                return 1  # Return index of inserted point
                
            # Calculate distances between points
            def distance(p1, p2):
                return math.sqrt((p1[0] - p2[0])**2 + (p1[1] - p2[1])**2)
            
            # Find the closest line segment to the new point
            min_dist = float('inf')
            insert_pos = 1  # Default to inserting after start point
            points = self.current_curve_points[:]
            
            # Check distance to each line segment
            for i in range(len(points) - 1):
                p1 = points[i]
                p2 = points[i + 1]
                
                # Calculate distance from point to line segment
                line_length = distance(p1, p2)
                if line_length == 0:
                    continue
                
                # Calculate projection of point onto line segment
                t = ((new_point[0] - p1[0]) * (p2[0] - p1[0]) +
                     (new_point[1] - p1[1]) * (p2[1] - p1[1])) / (line_length * line_length)
                
                # Find closest point on line segment
                if t < 0:
                    closest = p1
                elif t > 1:
                    closest = p2
                else:
                    closest = (p1[0] + t * (p2[0] - p1[0]),
                             p1[1] + t * (p2[1] - p1[1]))
                
                dist = distance(new_point, closest)
                print(f"Segment {i}: distance={dist}, current min={min_dist}")
                if dist < min_dist:
                    min_dist = dist
                    insert_pos = i + 1
            
            # Check if point is too close to existing points
            min_dist_to_points = min(distance(new_point, p) for p in points)
            print(f"Minimum distance to existing points: {min_dist_to_points}")
            if min_dist_to_points < 5 / self.total_scale:  # Minimum 5 pixels in screen space
                print(f"Point too close to existing points: {min_dist_to_points}")
                return None
                
            # Create a new list with all points
            new_points = []
            for i in range(len(points)):
                if i == insert_pos:
                    new_points.append(new_point)
                new_points.append(points[i])
            
            # Update current_curve_points with the new list
            self.current_curve_points = new_points
            print(f"Added point at position {insert_pos}. Total points: {len(self.current_curve_points)}")
            print(f"Final points: {self.current_curve_points}")
            return insert_pos
                
        except Exception as e:
            print(f"Error in add_and_sort_point: {str(e)}")
            print(f"Points when error occurred: {self.current_curve_points}")
            # Restore start and end points if there's an error
            if len(self.current_curve_points) >= 2:
                start_point = self.current_curve_points[0]
                end_point = self.current_curve_points[-1]
                self.current_curve_points = [start_point, end_point]
                print("Restored to start and end points only")
            return None

    def preview_curve(self):
        """Preview Bézier curve with proper coordinate conversion"""
        try:
            self.canvas.delete("preview")
            if len(self.current_curve_points) < 2:
                print("Not enough points for preview")
                return
            
            # Get curve color based on current plant
            curve_color = self.get_plant_color(self.current_plant)
            
            try:
                # Convert points to display coordinates
                display_points = []
                for point in self.current_curve_points:
                    try:
                        display_x = point[0] * self.total_scale
                        display_y = point[1] * self.total_scale
                        display_points.append((display_x, display_y))
                    except Exception as e:
                        print(f"Error converting point {point}: {str(e)}")
                        continue
                
                if len(display_points) < 2:
                    print("Not enough valid display points")
                    return
                
                # Generate Bézier curve in display coordinates
                curve_points = []
                try:
                    tangents = self.calculate_tangents(display_points)
                except Exception as e:
                    print(f"Error calculating tangents: {str(e)}")
                    return
                
                # Generate curve segments
                for i in range(len(display_points) - 1):
                    try:
                        p1 = display_points[i]
                        p2 = display_points[i+1]
                        segment_length = math.hypot(p2[0]-p1[0], p2[1]-p1[1])
                        control_length = segment_length * 0.4
                        
                        cp1 = (p1[0] + tangents[i][0] * control_length,
                              p1[1] + tangents[i][1] * control_length)
                        cp2 = (p2[0] - tangents[i+1][0] * control_length,
                              p2[1] - tangents[i+1][1] * control_length)
                        
                        # Generate smooth curve points
                        for t in np.linspace(0, 1, 50):
                            x = (1-t)**3 * p1[0] + 3*(1-t)**2 * t * cp1[0] + 3*(1-t) * t**2 * cp2[0] + t**3 * p2[0]
                            y = (1-t)**3 * p1[1] + 3*(1-t)**2 * t * cp1[1] + 3*(1-t) * t**2 * cp2[1] + t**3 * p2[1]
                            curve_points.append((x, y))
                    except Exception as e:
                        print(f"Error generating curve segment {i}: {str(e)}")
                        continue
                
                # Draw smooth curve
                if curve_points:
                    try:
                        coords = [coord for point in curve_points for coord in point]
                        self.canvas.create_line(
                            *coords,
                            smooth=True, fill=curve_color, width=2, tags="preview"
                        )
                    except Exception as e:
                        print(f"Error drawing curve: {str(e)}")
                else:
                    print("No curve points generated")
                    
            except Exception as e:
                print(f"Error in curve generation: {str(e)}")
                # Fallback to simple line if curve generation fails
                if len(display_points) >= 2:
                    try:
                        coords = [coord for point in display_points for coord in point]
                        self.canvas.create_line(
                            *coords,
                            smooth=True, fill=curve_color, width=2, tags="preview"
                        )
                    except Exception as e:
                        print(f"Error drawing fallback line: {str(e)}")
                        
        except Exception as e:
            print(f"Error in preview_curve: {str(e)}")

    def calculate_tangents(self, points):
        """Calculate tangent directions for Bézier control points"""
        n = len(points)
        tangents = []
        
        for i in range(n):
            if i == 0:
                dx = points[1][0] - points[0][0]
                dy = points[1][1] - points[0][1]
            elif i == n-1:
                dx = points[-1][0] - points[-2][0]
                dy = points[-1][1] - points[-2][1]
            else:
                dx1 = points[i][0] - points[i-1][0]
                dy1 = points[i][1] - points[i-1][1]
                dx2 = points[i+1][0] - points[i][0]
                dy2 = points[i+1][1] - points[i][1]
                dx = (dx1 + dx2) / 2
                dy = (dy1 + dy2) / 2
            
            length = math.hypot(dx, dy)
            if length > 0:
                dx /= length
                dy /= length
            tangents.append((dx, dy))
        
        return tangents

    def finish_drawing(self):
        """Finish the current drawing and save the curve"""
        try:
            if len(self.current_curve_points) < 2:
                messagebox.showwarning("Warning", "At least 2 points required!")
                return

            # Save the curve
            curve_data = {
                'type': self.current_type,
                'points': self.current_curve_points,
                'length': self.calculate_curve_length(self.current_curve_points)
            }
            
            if self.current_plant not in self.plants:
                self.plants[self.current_plant] = []
            self.plants[self.current_plant].append(curve_data)
            
            # Store the last drawing type for auto-continue feature
            self.last_drawing_type = self.current_type
            
            # Clear drawing state
            self.current_curve_points = []
            self.drawing_state = None
            self.current_type = None
            self.points_history = []
            self.redo_history = []
            
            # Update displays
            self.update_tree_view()
            self.redraw_all_curves()
            self.status_var.set(f"Drawing finished. Click to add another {self.last_drawing_type}")

        finally:
            # Always re-enable all buttons
            self.open_button.configure(state='normal')
            self.add_plant_button.configure(state='normal')
            self.add_root_button.configure(state='normal')
            self.add_stem_button.configure(state='normal')
            self.save_button.configure(state='normal')
            self.finish_button.configure(state='disabled')

    def draw_permanent_bezier(self, points, color, width=2, plant_id=None, idx=None):
        """Draw Bézier curve on canvas with specified width"""
        if len(points) < 2:
            return
        
        # Generate Bézier curve points with more interpolation points
        curve_points = []
        tangents = self.calculate_tangents(points)
        
        for i in range(len(points) - 1):
            p1 = points[i]
            p2 = points[i+1]
            segment_length = math.hypot(p2[0]-p1[0], p2[1]-p1[1])
            control_length = segment_length * 0.4  # Adjust control point distance
            
            # Calculate control points using tangents
            cp1 = (p1[0] + tangents[i][0] * control_length,
                p1[1] + tangents[i][1] * control_length)
            cp2 = (p2[0] - tangents[i+1][0] * control_length,
                p2[1] - tangents[i+1][1] * control_length)
            
            # Generate more points for smoother curves
            num_points = max(50, int(segment_length / 5))  # Adjust point density
            for t in np.linspace(0, 1, num_points):
                # Cubic Bézier curve formula
                x = (1-t)**3 * p1[0] + \
                    3*(1-t)**2 * t * cp1[0] + \
                    3*(1-t) * t**2 * cp2[0] + \
                    t**3 * p2[0]
                y = (1-t)**3 * p1[1] + \
                    3*(1-t)**2 * t * cp1[1] + \
                    3*(1-t) * t**2 * cp2[1] + \
                    t**3 * p2[1]
                curve_points.append((x, y))
        
        # Use provided IDs or default values
        plant_tag = f"plant_{plant_id}" if plant_id else "plant_unknown"
        curve_tag = f"curve_{idx}" if idx else "curve_unknown"
        
        # Draw the smooth curve
        if curve_points:
            # Convert points to flat coordinate list
            coords = [coord for point in curve_points for coord in point]
            self.canvas.create_line(
                *coords,
                fill=color,
                width=width,
                smooth=True,  # Enable smoothing
                splinesteps=50,  # Increase spline steps for smoother curves
                tags=("permanent", plant_tag, curve_tag)
            )
            
    def update_tree_view(self):
        """Update the tree view with current plant data"""
        self.tree.delete(*self.tree.get_children())
        
        for plant_id in self.plants:
            # Calculate max angle
            roots = [c for c in self.plants[plant_id] if c['type'] == 'root']
            stems = [c for c in self.plants[plant_id] if c['type'] == 'stem']
            max_angle, _, _ = self.calculate_angle(plant_id)
            
            # Calculate total lengths
            total_root_length = sum(r['length'] for r in roots)
            total_stem_length = sum(s['length'] for s in stems)
            
            # Create plant name with measurements
            plant_text = f"Plant {plant_id}"
            unit = self.get_unit_label()
            if roots:
                plant_text += f" - Roots: {total_root_length:.1f}{unit}"
            if stems:
                plant_text += f" - Stems: {total_stem_length:.1f}{unit}"
            if len(roots) >= 2 and max_angle > 0:
                plant_text += f" - Angle: {max_angle:.1f}°"
            
            # Insert plant item
            plant_item = self.tree.insert('', 'end', 
                                        text=plant_text, 
                                        values=("×",),
                                        open=True)
            
            # Add roots and stems
            for idx, curve in enumerate(self.plants[plant_id]):
                curve_text = f"{curve['type'].title()} {idx+1}: {curve['length']:.1f}{self.get_unit_label()}"
                self.tree.insert(plant_item, 'end', text=curve_text, values=("×",))

    def calculate_curve_length(self, points):
        """Calculate accurate length in mm using Bézier curve approximation"""
        if len(points) < 2:
            return 0
            
        try:
            # Generate Bézier curve points
            bezier_points = []
            
            # Calculate tangents for all points
            tangents = self.calculate_tangents(points)
            
            # Generate dense points along the curve for accurate length calculation
            for i in range(len(points) - 1):
                p1 = points[i]
                p2 = points[i+1]
                
                # Calculate control points using tangents
                segment_length = math.hypot(p2[0]-p1[0], p2[1]-p1[1])
                control_length = segment_length * 0.4
                
                cp1 = (p1[0] + tangents[i][0] * control_length,
                      p1[1] + tangents[i][1] * control_length)
                cp2 = (p2[0] - tangents[i+1][0] * control_length,
                      p2[1] - tangents[i+1][1] * control_length)
                
                # Generate points along the curve segment (more points for better accuracy)
                # Set higher number of points for more precise measurement
                num_points = max(50, int(segment_length * 3))
                
                for t in np.linspace(0, 1, num_points):
                    # Cubic Bézier curve formula
                    x = (1-t)**3 * p1[0] + 3*(1-t)**2 * t * cp1[0] + 3*(1-t) * t**2 * cp2[0] + t**3 * p2[0]
                    y = (1-t)**3 * p1[1] + 3*(1-t)**2 * t * cp1[1] + 3*(1-t) * t**2 * cp2[1] + t**3 * p2[1]
                    bezier_points.append((x, y))
                    
            # Calculate the actual curve length by summing distances between consecutive points
            curve_length = 0.0
            for i in range(len(bezier_points) - 1):
                x1, y1 = bezier_points[i]
                x2, y2 = bezier_points[i+1]
                curve_length += math.hypot(x2-x1, y2-y1)
                
            # Convert to mm using current scale
            return curve_length * self.get_current_scale()
        
        except Exception as e:
            print(f"Error calculating Bézier curve length: {str(e)}")
            # Fallback to original method if Bézier calculation fails
            pixel_length = 0
            for i in range(len(points)-1):
                x1, y1 = points[i]
                x2, y2 = points[i+1]
                pixel_length += math.hypot(x2-x1, y2-y1)
            return pixel_length * self.get_current_scale()

    def redraw_all_curves(self):
        """Redraw all curves with proper scaling"""
        self.canvas.delete("all")
        if self.photo_image:
            self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
        
        # Redraw all stored curves
        for plant_id, curves in self.plants.items():
            color = self.get_plant_color(plant_id)
            plant_name = f"Plant {plant_id}"
            first_root_start = None
            
            # Separate roots and stems
            roots = [c for c in curves if c['type'] == 'root']
            stemes = [c for c in curves if c['type'] == 'stem']
            
            # Draw roots
            for idx, curve in enumerate(curves):
                # Determine line width based on selection
                is_selected = (plant_id == self.selected_plant and 
                             idx == self.selected_curve)
                line_width = 4 if is_selected else 2
                
                display_points = [(x * self.total_scale, y * self.total_scale) 
                                for x, y in curve['points']]
                if len(display_points) >= 2:
                    curve_color = color if curve['type'] == 'root' else self.stem_color
                    self.draw_permanent_bezier(display_points, curve_color, 
                                             width=line_width, 
                                             plant_id=plant_id, idx=idx)
                    
                    # Position text based on curve type
                    end_x, end_y = display_points[-1]
                    mm_offset = 5 / self.get_current_scale()
                    if curve['type'] == 'root':
                        text_x = end_x + mm_offset
                        text_y = end_y
                    else:  # stem
                        text_x = end_x
                        text_y = end_y + mm_offset
                        
                    self.canvas.create_text(
                        text_x, text_y,
                        text=f"{curve['length']:.1f}{self.get_unit_label()}",
                        fill=curve_color,
                        font=('Arial', 10, 'bold')
                    )

            # Calculate and display angles between roots
            if len(roots) >= 2:
                max_angle, measure_points, start_points = self.calculate_angle(plant_id)
                if max_angle > 0:
                    # Convert measure points to display coordinates
                    disp_measure = [(x * self.total_scale, y * self.total_scale) 
                                  for x, y in measure_points]
                    
                    # Draw angle measurement
                    for point in disp_measure:
                        self.canvas.create_oval(
                            point[0]-3, point[1]-3,
                            point[0]+3, point[1]+3,
                            fill='black', outline='white'  # Changed from yellow to black
                        )
                    # Draw angle text
                    mid_x = sum(p[0] for p in disp_measure)/len(disp_measure)
                    mid_y = sum(p[1] for p in disp_measure)/len(disp_measure)
                    self.canvas.create_text(
                        mid_x, mid_y - 5,
                        text=f"{max_angle:.1f}°",
                        fill='black',  # Changed from yellow to black
                        font=('Arial', 12, 'bold')
                    )

    def calculate_angle(self, plant_id):
        """Calculate maximum angle between roots"""
        if plant_id not in self.plants:
            return 0, [], []
        
        roots = [c for c in self.plants[plant_id] if c['type'] == 'root']
        max_angle = 0
        measure_points = []
        start_points = []
        
        if len(roots) >= 2:
            for i in range(len(roots)):
                for j in range(i+1, len(roots)):
                    # Get vectors at 30mm from start
                    v1, p1 = self.get_vector_at_distance(roots[i]['points'], 30)
                    v2, p2 = self.get_vector_at_distance(roots[j]['points'], 30)
                    
                    if v1 and v2 and p1 and p2:
                        # Calculate vectors from start points
                        vec1 = (p1[0]-roots[i]['points'][0][0], 
                               p1[1]-roots[i]['points'][0][1])
                        vec2 = (p2[0]-roots[j]['points'][0][0], 
                               p2[1]-roots[j]['points'][0][1])
                        
                        # Calculate angle between vectors
                        angle = self.vector_angle(vec1, vec2)
                        if angle > max_angle:
                            max_angle = angle
                            measure_points = [p1, p2]
                            start_points = [roots[i]['points'][0], roots[j]['points'][0]]
        
        return max_angle, measure_points, start_points

    def get_vector_at_distance(self, points, distance_mm):
        """Get direction vector at specified distance from start, following the Bézier curve"""
        if not points:
            return None, None
        
        # Convert target distance from mm to pixels
        target_pixels = distance_mm / self.get_current_scale()
        
        # Generate Bézier curve points
        curve_points = []
        tangents = self.calculate_tangents(points)
        
        # Generate curve segments with high resolution
        for i in range(len(points) - 1):
            p1 = points[i]
            p2 = points[i+1]
            segment_length = math.hypot(p2[0]-p1[0], p2[1]-p1[1])
            control_length = segment_length * 0.4
            
            cp1 = (p1[0] + tangents[i][0] * control_length,
                  p1[1] + tangents[i][1] * control_length)
            cp2 = (p2[0] - tangents[i+1][0] * control_length,
                  p2[1] - tangents[i+1][1] * control_length)
            
            # Generate more points for accurate distance calculation
            for t in np.linspace(0, 1, 100):
                x = (1-t)**3 * p1[0] + 3*(1-t)**2 * t * cp1[0] + 3*(1-t) * t**2 * cp2[0] + t**3 * p2[0]
                y = (1-t)**3 * p1[1] + 3*(1-t)**2 * t * cp1[1] + 3*(1-t) * t**2 * cp2[1] + t**3 * p2[1]
                curve_points.append((x, y))
        
        # Calculate cumulative distance along the curve
        accumulated = 0
        for i in range(len(curve_points) - 1):
            p1 = curve_points[i]
            p2 = curve_points[i + 1]
            segment_length = math.hypot(p2[0]-p1[0], p2[1]-p1[1])
            
            if accumulated + segment_length >= target_pixels:
                # Found the segment containing our target point
                ratio = (target_pixels - accumulated) / segment_length
                point = (p1[0] + (p2[0] - p1[0]) * ratio,
                        p1[1] + (p2[1] - p1[1]) * ratio)
                
                # Calculate direction vector using nearby points for smoothness
                if i < len(curve_points) - 2:
                    next_point = curve_points[i + 2]
                else:
                    next_point = p2
                direction = (next_point[0] - p1[0], next_point[1] - p1[1])
                
                return direction, point
            
            accumulated += segment_length
        
        # If we haven't reached the target distance, use the last segment
        if curve_points:
            last_point = curve_points[-1]
            direction = (last_point[0] - curve_points[-2][0],
                        last_point[1] - curve_points[-2][1])
            return direction, last_point
        
        return None, None

    def vector_angle(self, v1, v2):
        """Calculate angle between two vectors in degrees"""
        dot = v1[0]*v2[0] + v1[1]*v2[1]
        mag1 = math.hypot(*v1)
        mag2 = math.hypot(*v2)
        
        if mag1 == 0 or mag2 == 0:
            return 0
        
        cos_theta = dot / (mag1 * mag2)
        return math.degrees(math.acos(max(min(cos_theta, 1), -1)))

    def undo_last_point(self, event=None):
        if not self.points_history:
            return
            
        # Get last action and save it for redo
        last_action = self.points_history.pop()
        self.redo_history.append(last_action)
        
        action_type, point = last_action
        
        if action_type == "start":
            # Undo start point
            self.current_curve_points = []
            self.drawing_state = "start"
            self.status_var.set("Select start point")
            self.finish_button.configure(state='disabled')
        elif action_type == "end":
            # Undo end point
            self.current_curve_points = self.current_curve_points[:1]
            self.drawing_state = "end"
            self.status_var.set("Select end point")
            self.finish_button.configure(state='disabled')
        elif action_type == "control":
            # Undo middle point
            # Rebuild point list, excluding last added point
            start_point = self.current_curve_points[0]
            end_point = self.current_curve_points[-1]
            middle_points = [p for p in self.current_curve_points[1:-1] if p != point]
            
            # Rebuild point list
            self.current_curve_points = [start_point] + middle_points + [end_point]
            
            
            self.drawing_state = "control"
            self.status_var.set("Select middle points or click Finish")
            self.finish_button.configure(state='normal')
            
        # Redraw current state
        self.redraw_current_curve()
        
    def redo_last_point(self, event=None):
        if not self.redo_history:
            return
            
        # Get last undone action
        action = self.redo_history.pop()
        action_type, point = action
        
        if action_type == "start":
            self.current_curve_points = [point]
            self.drawing_state = "end"
            self.status_var.set("Select end point")
        elif action_type == "end":
            self.current_curve_points.append(point)
            self.drawing_state = "control"
            self.status_var.set("Select middle points or click Finish")
            self.finish_button.configure(state='normal')
        elif action_type == "control":
            self.add_and_sort_point(point)
            
        # Add action back to history
        self.points_history.append(action)
        
        # Redraw current state
        self.redraw_current_curve()
        
    def redraw_current_curve(self):
        """Redraw current curve preview"""
        try:
            print("\n=== redraw_current_curve ===")
            print(f"Drawing state: {self.drawing_state}")
            print(f"Points to draw: {self.current_curve_points}")
            
            # Clear previous drawings
            self.canvas.delete("preview")
            self.canvas.delete("temp")
            
            # Safety check for current_curve_points
            if not hasattr(self, 'current_curve_points') or not self.current_curve_points:
                print("No curve points to draw")
                return
                
            # Draw control points
            for i, point in enumerate(self.current_curve_points):
                try:
                    # Convert point coordinates to display coordinates
                    display_x = point[0] * self.total_scale
                    display_y = point[1] * self.total_scale
                    
                    # Choose point color based on position
                    if i == 0:  # Start point
                        color = "red"
                    elif i == len(self.current_curve_points) - 1:  # End point
                        color = "green"
                    else:  # Middle points
                        color = "blue"
                    
                    print(f"Drawing point {i} at ({display_x}, {display_y}) in {color}")
                    
                    # Adjust size if point is being dragged
                    size = 5 if point == self.dragging_point else 3
                    
                    # Create point
                    self.canvas.create_oval(
                        display_x - size, display_y - size,
                        display_x + size, display_y + size,
                        fill=color, outline='white',
                        tags="temp"
                    )
                    
                    # Draw point number for debugging
                    self.canvas.create_text(
                        display_x + 10, display_y - 10,
                        text=str(i),
                        fill=color,
                        tags="temp"
                    )
                    
                except Exception as e:
                    print(f"Error drawing point {i}: {str(e)}")
                    continue
            
            # Draw curve if we have enough points
            if len(self.current_curve_points) >= 2:
                try:
                    print("Drawing preview curve")
                    self.preview_curve()
                except Exception as e:
                    print(f"Error drawing preview curve: {str(e)}")
            
            # Draw temporary line for guidance
            self.draw_temp_line()
            
        except Exception as e:
            print(f"Error in redraw_current_curve: {str(e)}")
            print(f"Current state when error occurred: {self.drawing_state}")
            print(f"Current points when error occurred: {self.current_curve_points}")
            # Try to recover the drawing state
            if hasattr(self, 'current_curve_points'):
                if len(self.current_curve_points) >= 2:
                    self.drawing_state = "control"
                elif len(self.current_curve_points) == 1:
                    self.drawing_state = "end"
                else:
                    self.drawing_state = "start"

    def on_drag(self, event):
        """Handle mouse drag during drawing"""
        try:
            print("\n=== on_drag ===")
            print(f"Drawing state: {self.drawing_state}")
            print(f"Current points before drag: {self.current_curve_points}")
            print(f"Dragging point index: {self.dragging_point_index}")
            
            # Check if Ctrl is pressed
            ctrl_pressed = event.state & 0x4
            
            # If Ctrl is pressed, don't do any drawing operations
            if ctrl_pressed:
                return
            
            # Convert to canvas coordinates then to image coordinates
            x = self.canvas.canvasx(event.x)
            y = self.canvas.canvasy(event.y)
            img_x = x / self.total_scale
            img_y = y / self.total_scale
            
            # Handle drawing state updates only when we have points and are in drawing state
            if self.drawing_state and self.current_curve_points:
                if self.dragging_point_index is not None:
                    # Update the newly added point
                    self.current_curve_points[self.dragging_point_index] = (img_x, img_y)
                    print(f"Updated point {self.dragging_point_index} to: ({img_x:.1f}, {img_y:.1f})")
                else:
                    # If no point is being dragged, update the last point (for end point placement)
                    self.current_curve_points[-1] = (img_x, img_y)
                    print(f"Updated last point to: ({img_x:.1f}, {img_y:.1f})")
                self.redraw_current_curve()
                self.draw_temp_line()
            
            print(f"Current points after drag: {self.current_curve_points}")
            
        except Exception as e:
            print(f"Error in on_drag: {str(e)}")
            print(f"Current state when error occurred: {self.drawing_state}")
            print(f"Current points when error occurred: {self.current_curve_points}")

    def toggle_background(self):
        """Toggle background image visibility"""
        self.show_background = not self.show_background
        self.canvas.delete("all")
        
        # Only show background image if show_background is True
        if self.show_background and self.photo_image:
            self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
            
        # Always redraw curves
        self.redraw_all_curves()

    def generate_curve_points(self, points):
        """Generate points for a smooth curve using Bezier interpolation"""
        if len(points) < 2:
            return []
            
        curve_points = []
        tangents = self.calculate_tangents(points)
        
        # Generate curve points for each pair of adjacent points
        for i in range(len(points) - 1):
            p1 = points[i]
            p2 = points[i + 1]
            
            # Calculate control points
            segment_length = math.sqrt((p2[0] - p1[0])**2 + (p2[1] - p1[1])**2)
            control_length = segment_length * 0.4
            
            cp1 = (p1[0] + tangents[i][0] * control_length,
                  p1[1] + tangents[i][1] * control_length)
            cp2 = (p2[0] - tangents[i+1][0] * control_length,
                  p2[1] - tangents[i+1][1] * control_length)
            
            # Generate curve points
            for t in np.linspace(0, 1, 30):
                x = (1-t)**3 * p1[0] + \
                    3*(1-t)**2 * t * cp1[0] + \
                    3*(1-t) * t**2 * cp2[0] + \
                    t**3 * p2[0]
                y = (1-t)**3 * p1[1] + \
                    3*(1-t)**2 * t * cp1[1] + \
                    3*(1-t) * t**2 * cp2[1] + \
                    t**3 * p2[1]
                curve_points.append((x, y))
                
        return curve_points
        
    def draw_curve(self, curve_points, color):
        """Draw a curve using the given points and color"""
        for i in range(len(curve_points)-1):
            self.canvas.create_line(
                curve_points[i][0] * self.scale_factor, 
                curve_points[i][1] * self.scale_factor,
                curve_points[i+1][0] * self.scale_factor, 
                curve_points[i+1][1] * self.scale_factor,
                fill=color, width=2
            )

    def confirm_delete_all(self):
        """Three-step confirmation for deleting all content"""
        response1 = messagebox.askyesno("Confirm Delete", 
                                      "Are you sure you want to delete all roots and stemes?")
        if response1:
            response2 = messagebox.askyesno("Second Confirmation", 
                                          "This will delete ALL your work. Are you really sure?")
            if response2:
                response3 = messagebox.askyesno("Final Confirmation", 
                                              "Last chance! Are you absolutely certain?")
                if response3:
                    self.delete_all()
                    
    def delete_all(self):
        """Delete all plants, roots and stemes"""
        if self.current_image_name and self.plants:
            self.save_backup()
            
        # Clear data
        self.plants.clear()
        self.plant_colors.clear()
        self.color_index = 0
        
        # Clear tree
        for item in self.tree.get_children():
            self.tree.delete(item)
            
        # Reset current selections
        self.current_plant = None
        self.current_curve_points = []
        self.drawing_state = None
        
        # Redraw canvas
        self.redraw_all_curves()
        
        # Show confirmation
        messagebox.showinfo("Deleted", "All content has been deleted.")

    def save_backup(self):
        """Save current measurements to backup file"""
        if not self.current_image_name or not self.current_image_dir:
            return
        
        backup_data = {
            'plants': {}
        }
        
        # Store points only, without calculated length
        for plant_id, curves in self.plants.items():
            backup_data['plants'][str(plant_id)] = []
            for curve in curves:
                backup_data['plants'][str(plant_id)].append({
                    'type': curve['type'],
                    'points': curve['points']  # Only store raw points
                })
        
        # Create label data directory if it doesn't exist
        label_data_dir = os.path.join(self.current_image_dir, "label data")
        os.makedirs(label_data_dir, exist_ok=True)
        
        # Get base name without extension
        base_name = os.path.splitext(self.current_image_name)[0]
        backup_file = os.path.join(label_data_dir, f"{base_name}.json")
        with open(backup_file, 'w') as f:
            json.dump(backup_data, f)
            
    def load_backup(self):
        """Load backup data and recalculate measurements"""
        if not self.current_image_name or not self.current_image_dir:
            return
        
        # Try loading from label data directory first
        label_data_dir = os.path.join(self.current_image_dir, "label data")
        base_name = os.path.splitext(self.current_image_name)[0]
        backup_file = os.path.join(label_data_dir, f"{base_name}.json")
        
        # If not found, try the old location
        if not os.path.exists(backup_file):
            backup_file = os.path.join(self.current_image_dir, f"{self.current_image_name}.json")
        
        if os.path.exists(backup_file):
            try:
                with open(backup_file, 'r') as f:
                    backup_data = json.load(f)
                
                # Load points and calculate lengths
                self.plants = {}
                for plant_id_str, curves in backup_data['plants'].items():
                    plant_id = int(plant_id_str)
                    self.plants[plant_id] = []
                    for curve in curves:
                        # Calculate curve length
                        pixel_length = sum(math.hypot(p2[0]-p1[0], p2[1]-p1[1]) 
                                        for p1, p2 in zip(curve['points'], curve['points'][1:]))
                        
                        self.plants[plant_id].append({
                            'type': curve['type'],
                            'points': curve['points'],
                            'length': pixel_length * self.get_current_scale()
                        })
                
                self.update_tree_view()
                self.redraw_all_curves()
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load backup: {str(e)}")

    def update_csv(self, action='add', curve_data=None, plant_name=None, curve_type=None):
        if not self.current_csv_file:
            return
            
        if action == 'add' and curve_data:
            with open(self.current_csv_file, 'a', newline='') as f:
                writer = csv.writer(f)
                writer.writerow([
                    self.current_image_name,
                    plant_name,
                    curve_data['type'],
                    f"{curve_data['length']:.2f}"
                ])
                
                if curve_data['type'] == 'root' and curve_data['angle'] > 0:
                    writer.writerow([
                        self.current_image_name,
                        plant_name,
                        'angle',
                        f"{curve_data['angle']:.2f}"
                    ])
                    
        elif action == 'delete':
            rows = []
            with open(self.current_csv_file, 'r', newline='') as f:
                reader = csv.reader(f)
                header = next(reader)
                rows = list(reader)
            
            if curve_type == 'all':
                rows = [row for row in rows if row[1] != plant_name]
            else:
                rows = [row for row in rows if not (
                    row[1] == plant_name and
                    (row[2] == curve_type or (curve_type == 'root' and row[2] == 'angle'))
                )]
            
            with open(self.current_csv_file, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerow(header)
                writer.writerows(rows)

    def run(self):
        self.mainloop()

    def restore_csv_from_backup(self):
        """Restore CSV records from backup data"""
        if not self.current_csv_file or not self.plants:
            return
            
        # Create new CSV file
        with open(self.current_csv_file, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['Image', 'Plant', 'Type', 'measure'])
            
            # Record all roots and stems data
            for plant_id, curves in self.plants.items():
                # Write all roots and stems data
                for curve_data in curves:
                    writer.writerow([
                        self.current_image_name,
                        plant_id,
                        curve_data['type'],
                        f"{curve_data['length']:.2f}"
                    ])
                
                # Calculate and write angle if there are multiple roots
                roots = [c for c in curves if c['type'] == 'root']
                if len(roots) >= 2:
                    max_angle, _, _ = self.calculate_angle(plant_id)
                    if max_angle > 0:
                        writer.writerow([
                            self.current_image_name,
                            plant_id,
                            'angle',
                            f"{max_angle:.2f}"
                        ])

    def save_current_csv(self):
        """Save current image data to CSV"""
        if not self.current_csv_file or not self.plants:
            return
            
        # Create new CSV file
        with open(self.current_csv_file, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['Image', 'Plant', 'Type', 'measure'])
            
            # Record all roots and stems data
            for plant_id, curves in self.plants.items():
                # Write all roots and stems data
                for curve_data in curves:
                    writer.writerow([
                        self.current_image_name,
                        plant_id,
                        curve_data['type'],
                        f"{curve_data['length']:.2f}"
                    ])
                
                # Calculate and write angle if there are multiple roots
                roots = [c for c in curves if c['type'] == 'root']
                if len(roots) >= 2:
                    max_angle, _, _ = self.calculate_angle(plant_id)
                    if max_angle > 0:
                        writer.writerow([
                            self.current_image_name,
                            plant_id,
                            'angle',
                            f"{max_angle:.2f}"
                        ])

    def save_all_data(self):
        """Save all measurement data to CSV"""
        if not self.current_image_name or not self.current_image_dir:
            return
        
        # Get base name without extension
        base_name = os.path.splitext(self.current_image_name)[0]
        csv_file = os.path.join(self.current_image_dir, f"{base_name}.csv")
        
        with open(csv_file, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            # Write header
            writer.writerow(['Image', 'Plant', 'Type', 'measure'])
            
            # Write data for each plant
            for plant_id, curves in self.plants.items():
                # Write all roots and stems data
                for curve_data in curves:
                    writer.writerow([
                        self.current_image_name,
                        plant_id,
                        curve_data['type'],
                        f"{curve_data['length']:.2f}"
                    ])
                
                # Calculate and write angle if there are multiple roots
                roots = [c for c in curves if c['type'] == 'root']
                if len(roots) >= 2:
                    max_angle, _, _ = self.calculate_angle(plant_id)
                    if max_angle > 0:
                        writer.writerow([
                            self.current_image_name,
                            plant_id,
                            'angle',
                            f"{max_angle:.2f}"
                        ])
        
        # Save backup
        self.save_backup()
        
        # Save labeled PNG
        self.save_labeled_png()
        
        messagebox.showinfo("Saved", f"All data saved to {csv_file}")
        
    def save_labeled_png(self):
        """Save a labeled PNG file with transparent background containing only the curves"""
        if not self.current_image_name or not self.current_image_dir or not self.original_image:
            return
            
        # Create label data directory if it doesn't exist
        label_data_dir = os.path.join(self.current_image_dir, "label data")
        os.makedirs(label_data_dir, exist_ok=True)
            
        # Get base name without extension
        base_name = os.path.splitext(self.current_image_name)[0]
        png_file = os.path.join(label_data_dir, f"{base_name}_label.png")
        
        # Create a transparent image with the same size as the original
        labeled_image = Image.new('RGBA', (self.original_image_width, self.original_image_height), (0, 0, 0, 0))
        draw = ImageDraw.Draw(labeled_image)
        
        # Draw all curves onto the image
        for plant_id, curves in self.plants.items():
            for curve in curves:
                # Generate Bézier curve points in the original image coordinates
                curve_points = []
                points = curve['points']
                
                if len(points) >= 2:
                    tangents = self.calculate_tangents(points)
                    
                    # Generate smooth curve points
                    for i in range(len(points) - 1):
                        p1 = points[i]
                        p2 = points[i+1]
                        segment_length = math.hypot(p2[0]-p1[0], p2[1]-p1[1])
                        control_length = segment_length * 0.4
                        
                        cp1 = (p1[0] + tangents[i][0] * control_length,
                              p1[1] + tangents[i][1] * control_length)
                        cp2 = (p2[0] - tangents[i+1][0] * control_length,
                              p2[1] - tangents[i+1][1] * control_length)
                        
                        # Generate many points for a smooth 1-pixel curve
                        num_points = max(100, int(segment_length * 3))
                        for t in np.linspace(0, 1, num_points):
                            x = (1-t)**3 * p1[0] + 3*(1-t)**2 * t * cp1[0] + 3*(1-t) * t**2 * cp2[0] + t**3 * p2[0]
                            y = (1-t)**3 * p1[1] + 3*(1-t)**2 * t * cp1[1] + 3*(1-t) * t**2 * cp2[1] + t**3 * p2[1]
                            curve_points.append((x, y))
                    
                    # Set color based on type (black for roots, green for stems)
                    if curve['type'] == 'root':
                        color = (0, 0, 0, 255)  # Black
                    else:  # stem
                        color = (0, 128, 0, 255)  # Green
                    
                    # Draw the curve with 1-pixel width
                    if len(curve_points) >= 2:
                        for i in range(len(curve_points) - 1):
                            draw.line(
                                [curve_points[i][0], curve_points[i][1], 
                                 curve_points[i+1][0], curve_points[i+1][1]],
                                fill=color, width=1
                            )
        
        # Save the labeled image
        labeled_image.save(png_file, format='PNG')

    def switch_to_previous_image(self, event=None):
        """Switch to the previous image"""
        try:
            if not self.current_image_path:
                return
            
            current_dir = os.path.dirname(self.current_image_path)
            # Get all image files
            all_files = [f for f in os.listdir(current_dir) if f.lower().endswith(('.png', '.jpg', '.jpeg'))]
            
            # Natural sort function for filenames
            def natural_sort_key(s):
                # Extract all numbers from the filename
                numbers = re.findall(r'\d+', s)
                if numbers:
                    # Check if numbers form a sequence
                    try:
                        # Convert first number found to int
                        return int(numbers[0])
                    except (ValueError, IndexError):
                        pass
                # Fallback to original string if no valid numbers found
                return s
            
            # Sort files using natural sort
            all_files.sort(key=natural_sort_key)
            current_index = all_files.index(self.current_image_name)
            
            if current_index > 0:
                prev_image = all_files[current_index - 1]
                if messagebox.askyesno("Switch Image", f"Switch to previous image ({prev_image})?"):
                    # Save current data
                    if self.plants:
                        self.save_all_data()
                    # Open previous image
                    self.open_specific_image(os.path.join(current_dir, prev_image))
            else:
                messagebox.showinfo("Info", "Already at first image")
        except ValueError:
            messagebox.showinfo("Info", "Current image not found in directory")
        except Exception as e:
            print(f"Error switching to previous image: {str(e)}")

    def switch_to_next_image(self, event=None):
        try:
            if not self.current_image_path:
                return
            
            current_dir = os.path.dirname(self.current_image_path)
            # Get all image files
            all_files = [f for f in os.listdir(current_dir) if f.lower().endswith(('.png', '.jpg', '.jpeg'))]
            
            # Natural sort function for filenames
            def natural_sort_key(s):
                # Extract all numbers from the filename
                numbers = re.findall(r'\d+', s)
                if numbers:
                    # Check if numbers form a sequence
                    try:
                        # Convert first number found to int
                        return int(numbers[0])
                    except (ValueError, IndexError):
                        pass
                # Fallback to original string if no valid numbers found
                return s
            
            # Sort files using natural sort
            all_files.sort(key=natural_sort_key)
            current_index = all_files.index(self.current_image_name)
            
            if current_index < len(all_files) - 1:
                next_image = all_files[current_index + 1]
                
                # Save current data with current image name
                if self.plants:
                    self.save_all_data()
                # Open next image
                self.open_specific_image(os.path.join(current_dir, next_image))
            else:
                messagebox.showinfo("Info", "Already at last image")
        except ValueError:
            messagebox.showinfo("Info", "Current image not found in directory")
        except Exception as e:
            print(f"Error switching to next image: {str(e)}")

    def open_specific_image(self, file_path):
        if os.path.exists(file_path):
            # Save current data if we have plants
            if self.plants and self.current_image_name:
                self.save_backup()
                self.save_current_csv()
                self.save_labeled_png()  # Save labeled PNG before switching
            
            # Store current view state
            old_zoom = self.display_zoom
            old_x = self.canvas.xview()[0]
            old_y = self.canvas.yview()[0]
            
            self.current_image_path = file_path
            self.current_image_dir = os.path.dirname(file_path)
            
            self.plants = {}
            self.current_curve_points = []
            self.points_history = []
            self.redo_history = []
            self.drawing_state = None
            self.current_type = None
            self.last_drawing_type = None
            self.current_plant = None
            self.selected_plant = None
            self.selected_curve = None
            
            self.tree.delete(*self.tree.get_children())
            
            self.canvas.delete("all")
            
            self.original_image = Image.open(file_path)
            self.original_image_width, self.original_image_height = self.original_image.size
            self.current_image = self.original_image.copy()
            
            # Restore zoom level
            self.display_zoom = old_zoom
            
            self.resize_image()
            self.current_image_name = os.path.basename(file_path)
            
            self.image_title.config(text=self.current_image_name)
            
            # Try to load backup from the new location
            base_name = os.path.splitext(self.current_image_name)[0]
            label_data_dir = os.path.join(self.current_image_dir, "label data")
            if os.path.exists(label_data_dir):
                backup_file = os.path.join(label_data_dir, f"{base_name}.json")
                if os.path.exists(backup_file):
                    self.load_backup()
            else:
                # Try the old location if the new one doesn't exist
                backup_file = os.path.join(self.current_image_dir, f"{self.current_image_name}.json")
                if os.path.exists(backup_file):
                    self.load_backup()
            
            contrast = float(self.contrast_scale.get())
            brightness = float(self.brightness_scale.get())
            
            enhanced = self.current_image.copy()
            enhanced = ImageEnhance.Contrast(enhanced).enhance(contrast)
            enhanced = ImageEnhance.Brightness(enhanced).enhance(brightness)
            
            # Add border to image
            bordered_image = self.add_border_to_image(enhanced)
            
            self.photo_image = ImageTk.PhotoImage(bordered_image)
            self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
            
            # Restore view position
            self.canvas.xview_moveto(old_x)
            self.canvas.yview_moveto(old_y)
            
            self.redraw_all_curves()

    def draw_import_line(self):
        window_width = self.width()
        window_height = self.height()
        
        start_x = int(window_width * self.import_line_start_ratio)
        start_y = int(window_height * self.import_line_height_ratio)
        end_x = int(window_width * self.import_line_end_ratio)
        end_y = start_y

        painter = QPainter(self)
        pen = QPen(Qt.black, 2)
        painter.setPen(pen)
        painter.drawLine(start_x, start_y, end_x, end_y)

    def get_current_scale(self):
        """Calculate current scale based on selected paper size"""
        if self.current_paper_size == 'Output pixels':
            return 1.0

        if not self.original_image:
            return 1.0
        
        shorter_side = min(self.original_image_width, self.original_image_height)
        
        if self.current_paper_size == 'Custom':
            reference_size = self.custom_size
        else:
            reference_size = PAPER_SIZES[self.current_paper_size]
            
        scale = reference_size / shorter_side
        # print(f"Current scale: {scale:.4f} mm/pixel (Reference: {reference_size}mm / {shorter_side}px)")
        return scale

    def get_unit_label(self):
        """Return the measurement unit label for the current paper size"""
        if self.current_paper_size == 'Output pixels':
            return 'px'
        return 'mm'

    def on_paper_size_change(self, event=None):
        """Handle paper size selection change"""
        selected_size = self.paper_size_var.get()
        self.current_paper_size = selected_size
        
        # Update custom size field when selecting predefined sizes
        if selected_size in PAPER_SIZES and selected_size not in ('Custom', 'Output pixels'):
            self.custom_size = PAPER_SIZES[selected_size]
            self.custom_size_var.set(str(self.custom_size))
            
        # Enable/disable custom size entry
        if selected_size == 'Custom':
            self.custom_size_entry.configure(state='normal')
        else:
            self.custom_size_entry.configure(state='disabled')

        # Disable custom size entry and set N/A for Output pixels
        if selected_size == 'Output pixels':
            self.custom_size_var.set('N/A')
            
        # Recalculate all measurements and redraw
        if self.current_image:
            # print("\nRecalculating all measurements with new paper size:")
            for plant in self.plants.values():
                for curve in plant:
                    # Recalculate curve length
                    pixel_length = sum(math.sqrt((p2[0]-p1[0])**2 + (p2[1]-p1[1])**2) 
                                     for p1, p2 in zip(curve['points'], curve['points'][1:]))
                    curve['length'] = pixel_length * self.get_current_scale()
                    # print(f" - {curve['type']} length updated to {curve['length']:.2f}mm")
            self.redraw_all_curves()

    def on_custom_size_change(self, *args):
        """Handle custom size entry change"""
        if self.paper_size_var.get() != 'Custom':
            return
            
        try:
            new_size = float(self.custom_size_var.get())
            if new_size > 0:
                self.custom_size = new_size
                # Update measurements if image is loaded
                if self.current_image:
                    self.redraw_all_curves()
        except ValueError:
            pass  # Ignore invalid input

    def zoom_in(self, event=None):
        # Get current view center
        x0, x1 = self.canvas.xview()
        y0, y1 = self.canvas.yview()
        old_center_x = (x0 + x1) / 2
        old_center_y = (y0 + y1) / 2
        
        self.display_zoom *= 1.1
        self.resize_image()
        self.redraw_all_curves()
        
        # Calculate new center position
        new_width = self.current_image.width
        new_height = self.current_image.height
        new_center_x = old_center_x * new_width
        new_center_y = old_center_y * new_height
        
        # Adjust view to maintain center
        self.canvas.xview_moveto(new_center_x/new_width - (x1 - x0)/2)
        self.canvas.yview_moveto(new_center_y/new_height - (y1 - y0)/2)
        
        self.status_var.set(f"Zoom: {self.display_zoom*100:.0f}%")

    def zoom_out(self, event=None):
        # Get current view center
        x0, x1 = self.canvas.xview()
        y0, y1 = self.canvas.yview()
        old_center_x = (x0 + x1) / 2
        old_center_y = (y0 + y1) / 2
        
        self.display_zoom = max(0.1, self.display_zoom*0.9)
        self.resize_image()
        self.redraw_all_curves()
        
        # Calculate new center position
        new_width = self.current_image.width
        new_height = self.current_image.height
        new_center_x = old_center_x * new_width
        new_center_y = old_center_y * new_height
        
        # Adjust view to maintain center
        self.canvas.xview_moveto(new_center_x/new_width - (x1 - x0)/2)
        self.canvas.yview_moveto(new_center_y/new_height - (y1 - y0)/2)
        
        self.status_var.set(f"Zoom: {self.display_zoom*100:.0f}%")

    def start_pan(self, event):
        """Start panning with middle mouse button"""
        self.canvas.scan_mark(event.x, event.y)
        self.canvas.config(cursor="fleur")

    def on_pan_drag(self, event):
        """Handle panning with middle mouse button"""
        if not self.drawing_state:  # Only pan if not drawing
            self.canvas.scan_dragto(event.x, event.y, gain=1)

    def end_pan(self, event):
        """End panning and restore cursor"""
        self.canvas.config(cursor="")

    def on_mouse_drag(self, event):
        """Handle mouse drag for drawing"""
        if self.drawing_state:
            # Convert canvas coordinates to image coordinates
            x = self.canvas.canvasx(event.x)
            y = self.canvas.canvasy(event.y)
            self.on_drag(event)  # Call the original drawing handler

    def on_mouse_move(self, event):
        if self.space_pressed:
            x = event.x
            y = event.y
            if self.last_pan_x and self.last_pan_y:
                dx = x - self.last_pan_x
                dy = y - self.last_pan_y
                self.canvas.xview_scroll(-dx, "units")
                self.canvas.yview_scroll(-dy, "units")
            self.last_pan_x = x
            self.last_pan_y = y

    def draw_temp_line(self):
        """Draw temporary control points during drawing only"""
        self.canvas.delete("temp")
        if self.drawing_state:
            for x, y in self.current_curve_points:
                display_x = x * self.total_scale
                display_y = y * self.total_scale
                self.canvas.create_oval(
                    display_x - 3, display_y - 3,
                    display_x + 3, display_y + 3,
                    fill='red', outline='white', tags="temp"
                )

    def on_tree_click(self, event):
        """Handle tree view click events"""
        # Identify which column was clicked
        region = self.tree.identify("region", event.x, event.y)
        if region == "cell":
            # Check if delete column was clicked
            column = self.tree.identify_column(event.x)
            if column == "#1":
                item = self.tree.identify_row(event.y)
                self.delete_item(item)

    def delete_item(self, item):
        """Delete selected item from tree and data"""
        if not item:
            return
        
        item_text = self.tree.item(item, "text")
        parent = self.tree.parent(item)

        # Confirm deletion
        if messagebox.askyesno("Delete", f"Delete {item_text}?"):
            # Handle plant deletion
            if "Plant" in item_text:
                plant_id = int(item_text.split()[1])
                if plant_id in self.plants:
                    del self.plants[plant_id]
            # Handle root/stem deletion
            elif parent and "Plant" in self.tree.item(parent, "text"):
                plant_id = int(self.tree.item(parent, "text").split()[1])
                curve_idx = int(item_text.split()[1].strip(":")) - 1
                if plant_id in self.plants and 0 <= curve_idx < len(self.plants[plant_id]):
                    del self.plants[plant_id][curve_idx]
            
            self.update_tree_view()
            self.redraw_all_curves()

    def on_release(self, event):
        """Handle mouse release event"""
        self.dragging_point = None
        self.dragging_point_index = None

    def cancel_drawing(self, event=None):
        """Cancel the current drawing without saving"""
        if self.drawing_state:
            # Clear current drawing data
            self.current_curve_points = []
            self.points_history = []
            self.redo_history = []
            self.drawing_state = None
            self.current_type = None
            
            # Re-enable all buttons
            self.open_button.configure(state='normal')
            self.add_plant_button.configure(state='normal')
            self.add_root_button.configure(state='normal')
            self.add_stem_button.configure(state='normal')
            self.save_button.configure(state='normal')
            self.finish_button.configure(state='disabled')
            
            # Clear temporary drawings
            self.canvas.delete("preview")
            self.canvas.delete("temp")
            
            # Update status
            self.status_var.set("Drawing cancelled")
            
            # Redraw all curves
            self.redraw_all_curves()

    def handle_q_shortcut(self, event):
        """Handle Q key shortcut for adding plant"""
        if not self.drawing_state:  # Only allow if not drawing
            self.add_plant()

    def handle_w_shortcut(self, event):
        """Handle W key shortcut for adding root"""
        if not self.drawing_state:  # Only allow if not drawing
            self.start_drawing('root')

    def handle_e_shortcut(self, event):
        """Handle E key shortcut for adding stem"""
        if not self.drawing_state:  # Only allow if not drawing
            self.start_drawing('stem')

    def handle_s_shortcut(self, event):
        """Handle S key shortcut for finishing drawing"""
        if self.drawing_state and len(self.current_curve_points) >= 2:
            self.finish_drawing()

if __name__ == "__main__":
    app = RootAnalyzer()
    app.run()


