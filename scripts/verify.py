import os
import subprocess
import tempfile
import json
import re

def eval_vercors(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".pvl", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "vercors:try", 
        "vct", container_file_path
    ]

    try:
        
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        
        completed = e
        timed_out = True

    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and completed.returncode == 2,
        "partial": not timed_out and (not (completed.returncode == 2) or  not (completed.returncode == 0))
    }

def eval_cbmc(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:

    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".c", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    
    container_file_path = f"/home/{filename}"

    
    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "cbmc:try", 
        "cbmc", "-z3", container_file_path,
    ]

    try:
        
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        
        completed = e
        timed_out = True


    os.unlink(f.name)

    match = re.search(r'\b(\d+)\s+of\s+(\d+)\s+failed\b', str(completed.stdout))
    partial = True
    none_verified = False
    if match:
        failed, total = int(match.group(1)), int(match.group(2))
        none_verified = failed == total
        partial = failed < total


    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0) and not none_verified,
        "timed_out": timed_out, 
        "compilation_err": (not timed_out) and (completed.returncode == 6),
        "partial": (not timed_out) and (not completed.returncode == 6) and partial
    }

    


def eval_verifast(code, timeout=5, language="java", max_errs=5, json_mode=True, func_name=None) -> dict:

    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=f".{language}", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "verifast:try", 
        "verifast", "-c", "-disable_overflow_check", container_file_path
    ]

    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    match = re.search(r'(\d+)\s+errors\s+found\s+\((\d+)\s+statements\s+verified\)', str(completed.stdout))

    partial = True
    goals = False
    if match:
        errors = int(match.group(1))
        verified = int(match.group(2))
        partial = (errors != 0)
        goals = verified > 0

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0) and not partial and goals,
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and (completed.returncode == 1),
        "partial": not timed_out and partial and goals 
    }


def eval_why3(code, timeout=60, timelimit=10, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".mlw", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
  
    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "why3:try", 
        "why3", "prove", "-P", "cvc4", "--timelimit", f"{timelimit}", container_file_path
    ]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out, 
        "compilation_err":not timed_out and (completed.returncode == 1),
        "partial": (not timed_out and completed.returncode == 2)
    }


def eval_dafny(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".dfy", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    
    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "dafny:try", 
        "dafny", "verify", "--allow-warnings", container_file_path
    ]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True


    os.unlink(f.name)


    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 2),
        "partial": not timed_out and (completed.returncode == 4)

    }


def eval_verus(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:

    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".dfy", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    multiple_errors = f"--multiple-errors {max_errs}" if max_errs > 0 else ""
    err_format = "--output-json --error-format=json" if json_mode else ""
    cmd = (f"/verus/verus {multiple_errors} {err_format}").split(" ")
    cmd += [filename]
    if func_name:
        cmd += ["--verify-function", func_name, "--verify-root"]


    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home", "verus:try"] + cmd
    
    try:
        
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        
        completed = e
        timed_out = True


    os.unlink(f.name)


    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 1),
        "partial": not timed_out and (completed.returncode != 0) and  (completed.returncode != 1)
    }



def eval_framac(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".c", dir=tmp_dir, delete=False) as f:
        f.write(code)
        filename = os.path.basename(f.name)
    

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker", "run", "--rm",
        "-v", f"{tmp_dir}:/home",
        "-w", "/home",
        "framac:try", 
        "frama-c", "-wp", "-wp-rte", "-wp-prover", "alt-ergo", container_file_path
    ]
    try:
        
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        
        completed = e
        timed_out = True


    os.unlink(f.name)

    partial = True
    no_goal = True
    match = re.search(r'Proved goals:\s+(\d+)\s*/\s*(\d+)', str(completed.stdout))
    if match:
        proved, total = int(match.group(1)), int(match.group(2))
        no_goal = total == 0
        partial = proved < total 


    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0) and (not partial) and (not no_goal),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode != 0),
        "partial": not timed_out and (partial or no_goal),
    }