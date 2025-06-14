from flask import Blueprint, render_template, request, jsonify, send_file, make_response
import json
from pathlib import Path
from datetime import datetime
import os
import subprocess
import tempfile
import uuid
import threading
from queue import Queue
import time

# Create blueprints
main_bp = Blueprint('main', __name__)
editor_bp = Blueprint('editor', __name__, url_prefix='/editor')
generator_bp = Blueprint('generator', __name__, url_prefix='/generator')
viewer_bp = Blueprint('viewer', __name__, url_prefix='/viewer')

# Store generated schedules and tasks
GENERATED_SCHEDULES = []
TASKS = {}

def run_scheduler_task(task_id, config_file, timeslot_file, output_file):
    try:
        # Run the scheduler executable
        result = subprocess.run(
            ['scheduler', str(config_file), '--timeslot-config', str(timeslot_file), '--format', 'json', '--output', str(output_file)],
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            # Read the generated schedule
            with open(output_file, 'r') as f:
                schedule_data = json.load(f)
            
            if not schedule_data:
                TASKS[task_id]['status'] = 'error'
                TASKS[task_id]['error'] = 'No schedule generated'
                return
            
            # Create schedule entry
            schedule_id = len(GENERATED_SCHEDULES)
            schedule = {
                'id': schedule_id,
                'timestamp': datetime.now().isoformat(),
                'data': schedule_data[0] if isinstance(schedule_data, list) else schedule_data
            }
            GENERATED_SCHEDULES.append(schedule)
            
            # Update task status
            TASKS[task_id]['status'] = 'completed'
            TASKS[task_id]['schedule_id'] = schedule_id
        else:
            # Update task status with error
            TASKS[task_id]['status'] = 'error'
            TASKS[task_id]['error'] = result.stderr or 'Unknown error occurred'
            
    except Exception as e:
        # Update task status with error
        TASKS[task_id]['status'] = 'error'
        TASKS[task_id]['error'] = str(e)
    finally:
        # Clean up temporary files
        try:
            config_file.unlink(missing_ok=True)
            timeslot_file.unlink(missing_ok=True)
            output_file.unlink(missing_ok=True)
        except:
            pass

@main_bp.route('/')
def index():
    return render_template('index.html')

# Course Editor Routes
@editor_bp.route('/courses')
def course_editor():
    return render_template('editor/courses.html')

@editor_bp.route('/courses/save', methods=['POST'])
def save_courses():
    data = request.json
    # Ensure the data structure matches what the template expects
    if not isinstance(data, dict):
        return jsonify({'error': 'Invalid data format'}), 400
    
    required_sections = ['rooms', 'labs', 'faculty', 'courses']
    for section in required_sections:
        if section not in data:
            data[section] = []
    
    with open('courses.json', 'w') as f:
        json.dump(data, f, indent=2)
    return jsonify({'status': 'success'})

@editor_bp.route('/courses/load')
def load_courses():
    try:
        with open('courses.json', 'r') as f:
            data = json.load(f)
            # Ensure all required sections exist
            required_sections = ['rooms', 'labs', 'faculty', 'courses']
            for section in required_sections:
                if section not in data:
                    data[section] = []
            return jsonify(data)
    except FileNotFoundError:
        # Return empty data structure if file doesn't exist
        return jsonify({
            'rooms': [],
            'labs': [],
            'faculty': [],
            'courses': []
        })

# Time Slots Editor Routes
@editor_bp.route('/times')
def time_editor():
    return render_template('editor/times.html')

@editor_bp.route('/times/save', methods=['POST'])
def save_times():
    data = request.json
    # Validate the data structure
    if not isinstance(data, dict) or 'times' not in data:
        return jsonify({'error': 'Invalid data format'}), 400
    
    required_days = ['MON', 'TUE', 'WED', 'THU', 'FRI']
    for day in required_days:
        if day not in data['times']:
            data['times'][day] = []
    
    with open('time_slots.json', 'w') as f:
        json.dump(data, f, indent=2)
    return jsonify({'status': 'success'})

@editor_bp.route('/times/load')
def load_times():
    try:
        with open('time_slots.json', 'r') as f:
            data = json.load(f)
            # Ensure all required days exist
            required_days = ['MON', 'TUE', 'WED', 'THU', 'FRI']
            for day in required_days:
                if day not in data['times']:
                    data['times'][day] = []
            return jsonify(data)
    except FileNotFoundError:
        # Return empty data structure if file doesn't exist
        return jsonify({
            'times': {
                'MON': [],
                'TUE': [],
                'WED': [],
                'THU': [],
                'FRI': []
            }
        })

# Schedule Generator Routes
@generator_bp.route('/')
def generator():
    return render_template('generator/index.html')

@generator_bp.route('/generate', methods=['POST'])
def generate_schedule():
    data = request.json
    
    # Create temporary files for input and output
    temp_dir = Path('temp')
    temp_dir.mkdir(exist_ok=True)
    
    # Generate unique filenames and task ID
    unique_id = str(uuid.uuid4())
    config_file = temp_dir / f'config_{unique_id}.json'
    timeslot_file = temp_dir / f'timeslot_{unique_id}.json'
    output_file = temp_dir / f'output_{unique_id}.json'
    
    try:
        # Write config data to temporary file
        with open(config_file, 'w') as f:
            json.dump(data.get('config', {}), f, indent=2)
            
        # Write timeslot data to temporary file
        with open(timeslot_file, 'w') as f:
            json.dump(data.get('timeslots', {}), f, indent=2)
        
        # Create task entry
        task_id = str(uuid.uuid4())
        TASKS[task_id] = {
            'status': 'running',
            'start_time': datetime.now().isoformat(),
            'config': data.get('config', {}),
            'timeslots': data.get('timeslots', {})
        }
        
        # Start background task
        thread = threading.Thread(
            target=run_scheduler_task,
            args=(task_id, config_file, timeslot_file, output_file)
        )
        thread.start()
        
        return jsonify({
            'task_id': task_id,
            'status': 'running'
        })
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@generator_bp.route('/task/<task_id>')
def check_task_status(task_id):
    if task_id not in TASKS:
        return jsonify({'error': 'Task not found'}), 404
    
    task = TASKS[task_id]
    response = {
        'status': task['status']
    }
    
    if task['status'] == 'completed':
        response['schedule_id'] = task['schedule_id']
    elif task['status'] == 'error':
        response['error'] = task['error']
    
    return jsonify(response)

@generator_bp.route('/history')
def schedule_history():
    return jsonify(GENERATED_SCHEDULES)

@generator_bp.route('/download/<int:schedule_id>')
def download_schedule(schedule_id):
    if schedule_id >= len(GENERATED_SCHEDULES):
        return jsonify({'error': 'Schedule not found'}), 404
    
    schedule = GENERATED_SCHEDULES[schedule_id]
    
    # Create the response with the raw schedule data
    response = make_response(jsonify(schedule['data']))
    response.headers['Content-Disposition'] = f'attachment; filename=schedule_{schedule_id}.json'
    response.headers['Content-Type'] = 'application/json'
    
    return response

# Schedule Viewer Routes
@viewer_bp.route('/')
def viewer():
    return render_template('viewer/index.html')

@viewer_bp.route('/upload', methods=['POST'])
def upload_schedule():
    if 'file' not in request.files:
        return jsonify({'error': 'No file provided'}), 400
    
    file = request.files['file']
    if file.filename == '':
        return jsonify({'error': 'No file selected'}), 400
    
    try:
        schedule = json.load(file)
        return jsonify(schedule)
    except json.JSONDecodeError:
        return jsonify({'error': 'Invalid JSON file'}), 400

@viewer_bp.route('/view/<int:schedule_id>')
def view_schedule(schedule_id):
    if schedule_id >= len(GENERATED_SCHEDULES):
        return jsonify({'error': 'Schedule not found'}), 404
    
    schedule = GENERATED_SCHEDULES[schedule_id]
    return jsonify(schedule['data'])