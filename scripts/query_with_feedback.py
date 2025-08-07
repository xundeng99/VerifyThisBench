import os
import json
import argparse
from openai import OpenAI
import time

### Set up clinet
client = OpenAI(azure_endpoint=api_base, api_key=api_key, api_version=api_version)

def chat_completion(messages, model="4o-mini", temperature=0.7):
    response = client.chat.completions.create(
        model=model,
        messages=messages,
        temperature=temperature,
    )
    return response.choices[0].message.content

def extract_code(response):
    for tag in ["```code", "```dafny", "```c", "```whyml", "```java",  "```cmbc", "```why3", "```rust","```"]:
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
    return chat_completion(messages)

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
    parser.add_argument("--tool", type=str, required=True, help="Formal verification tool name")
    parser.add_argument("--attempt", type=int, required=True, help="Attempt for each task")
    parser.add_argument("--timelimit", type=int, required=True, help="Time limit to run the tool")

    args = parser.parse_args()
    tool = args.tool
    attempt_limit = args.attempt
    time_limit = args.timelimit

    system_prompt_file = f"../prompts/system_prompts/{tool}.txt"
    assert os.path.exists(system_prompt_file), f"Missing system prompt file: {system_prompt_file}"
    system_prompt = open(system_prompt_file).read()
    coherent_prompt_file = "../prompts/coherent_prompt.txt"
    with open(coherent_prompt_file, "r") as f:
        coherent_prompt = f.read()

    task_root = "../VerifyThisBench/all"
    log_root = f"../gpt4omini/results_{tool}_feedback"
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

            print(f"\nProcessing {year}/{taskname}")
            log_dir = os.path.join(log_root, year, taskname)
            os.makedirs(log_dir, exist_ok=True)

            # Read task description
            description_path = os.path.join(task_path, "description.txt")
            if not os.path.exists(description_path):
                print(f"Missing description.txt for {year}/{taskname}, skipping.")
                continue

            with open(description_path) as f:
                description = f.read()

            task_context = [
                {"role": "user", "content": f"Target this verification problem; plan out your steps and write your final answer:\n\n{description}"},
                {"role": "assistant", "content": "OK, I'm ready to help."}
            ]

            tasks = read_tasks_in_order(task_path)

            for idx, task in enumerate(tasks):
                print(f"Generating for {task['file']}")
                attempt = 1
                error = None
                starttime = time.time()
                while attempt <= attempt_limit:
                    start = time.time()
                    # Refine context = previous task context + previous refinements of current task
                    refine_context = task_context.copy() if attempt == 1 else refine_context
                    query_inst = task["content"] if attempt == 1 else error_feedback_inst + f"{error}"
                    
                    response = form_query_response(query_inst, system_prompt, task_context)
                        
                    code_response, tag = extract_code(response)
                    code_response_time = time.time()
                    print(f"Attemp {attempt} code response: {code_response_time - start}s")

                    log_dir = os.path.join(log_root, year, taskname, str(idx+1))
                    os.makedirs(log_dir, exist_ok=True)

                    # Save code
                    code_path = os.path.join(log_dir, f"code_response_{idx + 1}_{attempt}.txt")
                    save_to_file(code_path, code_response or "NO CODE FOUND")

                    # Save context
                    refine_context.extend([
                        {"role": "user", "content": query_inst},
                        {"role": "assistant", "content": response}                   ])
                    context_path = os.path.join(log_dir, f"refine_context_{idx + 1}_{attempt}.txt")
                    save_to_file(context_path, json.dumps(refine_context, indent=4))

                    # Save coherence
                    coherence_check = form_query_response(coherent_prompt, system_prompt, task_context + [
                        {"role": "user", "content":  task["content"]},
                        {"role": "assistant", "content": response}                   ])
                    coherence_response = extract_coherence(coherence_check)
                    coherence_response_time = time.time()
                    print(f"Attemp {attempt} coherence response: {coherence_response_time - code_response_time}s")
                    correctness_path = os.path.join(log_dir, f"coherence_check_{idx + 1}_{str(attempt)}.txt")
                    save_to_file(correctness_path, coherence_check, coherence_response or "NO COHERENCE FOUND")


                    verification_path = os.path.join(log_dir, f"verification_{idx + 1}_{str(attempt)}.txt")
                    if not code_response:
                        attempt += 1
                        error = "Your previous attemp did not contain any code."
                        save_to_file(verification_path, json.dumps("NO CODE FOUND"))
                        continue

                    print(f"\nVerifying {year}/{taskname}/task{idx + 1} / attempt{str(attempt)}")

                    start = time.time()
                    result = eval_code(tool, code_response, tag, time_limit)
                    print(f"Attemp {attempt} evaluation: {time.time() - start}s")
                    save_to_file(verification_path, json.dumps(result, indent=2))
                    error = result["out"]+ result["err"] if not result["timed_out"] else "Execution timed out."
                    # early stop is succeed and all goals verified.
                    # need partial as some tool return 0 when goals partially verified.
                    if result["succeed"] and not result["partial"]:
                        task_context.extend([
                        {"role": "user", "content": task["content"]},
                        {"role": "assistant", "content": response}     ])
                        task_context_path = os.path.join(log_dir, f"task_context_{idx + 1}_{attempt}.txt")
                        save_to_file(task_context_path, json.dumps(task_context, indent=4))
                        break
                    
                    # Last attempt
                    if attempt == attempt_limit:
                        task_context.extend([
                        {"role": "user", "content": task["content"]},
                        {"role": "assistant", "content": response}     ])
                        task_context_path = os.path.join(log_dir, f"task_context_{idx + 1}_{attempt}.txt")
                        save_to_file(task_context_path, json.dumps(task_context, indent=4))
                        print("Saving current context")

                    attempt += 1
                print(f"Complete task elapsed {time.time() - starttime}")
                    

if __name__ == "__main__":
    main()
    