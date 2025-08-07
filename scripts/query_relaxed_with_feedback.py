import os
import json
import argparse
from openai import OpenAI
import time

# Set up API client
client = OpenAI(azure_endpoint=api_base, api_key=api_key, api_version=api_version)

def chat_completion(messages, model="4o-mini", temperature=0.7):
    response = client.chat.completions.create(
        model=model,
        messages=messages,
        temperature=temperature,
    )
    return response.choices[0].message.content

def extract_code(response):
    for tag in ["```code", "```dafny", "```c", "```whyml", "```java",  "```cmbc", "```why3", "```rust", "```"]:
        start = response.find(tag)
        if start != -1:
            end = response.find("```", start + len(tag))
            if end != -1:
                return response[start + len(tag):end].strip(), tag[3:]
    return None, None

def extract_coherence(response):
    start = response.find("/answer{")
    end = response.find("}", start)
    if start != -1 and end != -1:
        return response[start + len("/answer{"):end].strip()
    return None

def form_query_response(instruction, system_prompt, previous_context=None):
    messages = [{"role": "system", "content": system_prompt}]
    if previous_context:
        messages.extend(previous_context)
    messages.append({"role": "user", "content": instruction})
    return chat_completion(messages, model="claude-3-7-sonnet-20250219")

def read_tasks_in_order(folder_path):
    task_files = sorted(
        [f for f in os.listdir(folder_path) if f.startswith("task") and f.endswith(".txt")],
        key=lambda x: int(x.split("task")[1].split(".txt")[0])
    )
    return [{"file": f, "content": open(os.path.join(folder_path, f)).read()} for f in task_files]

def save_to_file(path, *contents):
    with open(path, "w") as f:
        for content in contents:
            f.write(content)
            f.write("\n\n")

def eval_code(tool, code_string, tag, timeout=60):
    if tool == "verus":
        from verify import eval_verus as eval_verus
        return eval_verus(code_string, timeout)
    elif tool == "why3":
        from verify import eval_why3 as eval_why3
        return eval_why3(code_string, timeout)
    elif tool == "dafny":
        from verify import eval_dafny as eval_dafny
        return eval_dafny(code_string, timeout)
    elif tool == "framac":
        from verify import eval_framac as eval_framac
        return eval_framac(code_string, timeout) 
    elif tool == "verifast":
        from verify import eval_verifast as eval_verifast
        return eval_verifast(code_string, timeout, tag)
    elif tool == "vercors":
        from verify import eval_vercors as eval_vercors
        return eval_vercors(code_string, timeout)
    elif tool == "cbmc":
        from verify import eval_cbmc as eval_cbmc
        return eval_cbmc(code_string, timeout)
    else:
        return {"error": f"No eval implementation for tool: {tool}", "returncode": -1}

# === Main ===
def main():
    
    parser = argparse.ArgumentParser()
    parser.add_argument("--attempt", type=int, required=True, help="Attempt for each task")
    parser.add_argument("--timelimit", type=int, required=True, help="Time limit to run the tool")

    args = parser.parse_args()
    attempt_limit = args.attempt
    time_limit = args.timelimit

    coherent_prompt_file = "../prompts/coherent_prompt.txt"
    with open(coherent_prompt_file, "r") as f:
        coherent_prompt = f.read()

    task_root = "../VerifyThisBenchXS"
    log_root = "../claude/results_relaxed_feedback"

    fill_todo_inst = "Complete the TODO fields in the solution template. Fix any potential syntax error as necessary. \n"
    error_feedback_inst = "Here is the error log. Fix the issues. \n"

    #================ GENERATION ======================

    for year in sorted(os.listdir(task_root)):
        year_path = os.path.join(task_root, year)
        if not os.path.isdir(year_path):
            continue

        for taskname in sorted(os.listdir(year_path)):
            task_path = os.path.join(year_path, taskname)
            if not os.path.isdir(task_path):
                continue

            for tool in os.listdir(task_path):                
                tool_path = os.path.join(task_path, tool)
                print(f"\nProcessing {year}/{taskname}/{tool}")
                log_dir = os.path.join(log_root, year, taskname, tool)
                os.makedirs(log_dir, exist_ok=True)

                # Read task description
                description_path = os.path.join(tool_path, "description.txt")
                if not os.path.exists(description_path):
                    print(f" Missing description.txt for {year}/{taskname}, skipping.")
                    continue

                description = open(description_path).read()

                system_prompt_file = f"../prompts/system_prompts/{tool}.txt"
                assert os.path.exists(system_prompt_file), f"Missing system prompt file: {system_prompt_file}"
                system_prompt = open(system_prompt_file).read()

                for filename in sorted(os.listdir(tool_path)):
                    # Skip the two special cases:
                    if filename == "description.txt":
                        continue
                    name, _ext = os.path.splitext(filename)
                    if name == "solution":
                        continue
                    
                    full_path = os.path.join(tool_path, filename)
                    if not os.path.isfile(full_path):
                        continue

                    template_solution = None
                    # Read the file
                    with open(full_path, 'r', encoding='utf-8') as f:
                        template_solution = f.read()
                         

                    task_context = [
                        {"role": "user", "content": f"Target this verification problem; plan out your steps and write your final answer:\n\n{description}. Your task is to complete a given template solution and fill in the TODO fields"},
                        {"role": "assistant", "content": "OK, I'm ready to help."}
                    ]

              
                    print(f"Generating for {year}/{taskname}/{tool}/{filename}")

                    attempt = 1
                    error = None


                    starttime = time.time()

                    
                    while attempt <= attempt_limit:
                        start = time.time()
                        refine_context = task_context.copy() if attempt == 1 else refine_context
                        query_inst = fill_todo_inst + f"{template_solution}" if attempt == 1 else error_feedback_inst + f"{error}"
                     
                        response = form_query_response(query_inst, system_prompt, refine_context)
                            
                        code_response, tag = extract_code(response)
                        print(f"Generation takes {time.time() - start}s")
                        log_dir = os.path.join(log_root, year, taskname, tool, str(attempt))
                        os.makedirs(log_dir, exist_ok=True)
                        # Save code
                        code_path = os.path.join(log_dir, f"code_response_{filename}_{str(attempt)}")
                        save_to_file(code_path, code_response or "NO CODE FOUND")

                        # Save context
                        refine_context.extend([
                            {"role": "user", "content": query_inst + template_solution},
                            {"role": "assistant", "content": response}
                        ])
                        refine_context_path = os.path.join(log_dir, f"refine_context_{filename}_{str(attempt)}.txt")
                        save_to_file(refine_context_path, json.dumps(refine_context, indent=4))

                        # Save coherence
                        # Coherence context is the task description + template solution
                        start = time.time()
                        time.sleep(5)
                        coherence_check = form_query_response(coherent_prompt, system_prompt, task_context +\
                                                              [{"role": "user", "content":fill_todo_inst + f"{template_solution}"}, 
                                                               {"role": "assistant", "content": response}])
                        print(f"Coherence takes {time.time() - start}s")
                        coherence_response = extract_coherence(coherence_check)
                        correctness_path = os.path.join(log_dir, f"coherence_check_{filename}_{str(attempt)}.txt")
                        save_to_file(correctness_path, coherence_check, coherence_response or "NO COHERENCE FOUND")

                        verification_path = os.path.join(log_dir, f"verification_{filename}_{str(attempt)}.txt")
                        if not code_response:
                            attempt += 1
                            error = "Your previous attemp did not contain any code."
                            save_to_file(verification_path, json.dumps("NO CODE FOUND"))
                            continue

                        print(f"\nVerifying {year}/{taskname}/{filename}/{str(attempt)}")

                        start = time.time()
                        result = eval_code(tool, code_response, tag, time_limit)
                        print(f"Evaluation takes {time.time() - start}s")
                        save_to_file(verification_path, json.dumps(result, indent=2))
                        error = result["out"]+result["err"] if not result["timed_out"] else "Execution timed out."
                        # early stop is succeed and all goals verified.
                        # need partial as some tool return 0 when goals partially verified.
                        if result["succeed"] and not result["partial"]:
                            break
                        attempt += 1
                        time.sleep(5)
                    print(f"Task completed in {time.time() - starttime}s")
                    

if __name__ == "__main__":
    main()
    