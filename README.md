# VerifyThisBench: Generating Code, Specifications, and Proofs All at Once
**VerifyThisBench**, inspired by the annual VerifyThis Competition, is a new benchmark designed to evaluate LLMs on end-to-end program verification tasks that require interpreting natural language problem descriptions, formulating formal specifications, generating code, and constructing correctness proofs. 

We also provide **VerifyThisBenchXS**, a relaxed variant where partial solution is provided. 

Read the paper: [arXiv:2505.19271](https://arxiv.org/abs/2505.19271)

### 🏆 Leaderboards

#### VerifyThisBench 

| Rank | Model       | Zero-shot | Refinement |
|------|-------------|-----------|------------|
| 1    | o3-mini     | 3.62%     | **9.37%**  |
| 2    | Claude      | 2.32%     | 7.98%      |
| 3    | o4-mini     | 0.93%     | 7.98%      |
| 4    | Llama       | 3.34%     | 7.88%      |
| 5    | Gemini      | 1.48%     | 6.86%      |
| 6    | GPT-4o      | 1.48%     | 6.22%      |
| 7    | Deepseek    | 1.02%     | 5.19%      |
| 8    | GPT-4o-mini | 2.23%     | 4.64%      |
| 9    | Qwen        | 0.28%     | 1.11%      |

#### VerifyThisBenchXS

| Rank | Model       | Zero-shot | Refinement |
|------|-------------|-----------|------------|
| 1    | Deepseek    | 2.49%     | **16.01%** |
| 2    | o4-mini     | 1.25%     | 14.55%     |
| 3    | Claude      | 1.46%     | 13.10%     |
| 4    | Llama       | 0.62%     | 11.23%     |
| 5    | GPT4o       | 1.04%     | 8.52%      |
| 6    | o3-mini     | 1.04%     | 6.44%      |
| 7    | GPT4o-mini  | 0.83%     | 3.53%      |
| 8    | Gemini      | 0.83%     | 3.53%      |
| 9    | Qwen        | 0.62%     | 2.70%      |


### Dataset structure
- `/VerifyThisBench`: Main benchmark organized by **year**
  - Each challenge includes:
    - `description.txt`: natural language problem statement
    - Sub-task files for implementation, specification, and invariants

- `/VerifyThisBenchXS`: Relaxed benchmark with **partial solutions**
  - Organized by **year** and **tool**
  - Variants include:
    - `fill-implementation`, `fill-specification`, `fill-loop-invariant`
    - Files with `split` provide partial input to the LLM
    - `solution.*`: human-written reference solution

- Other directories:
  - `/prompts`: example system and instruction prompts
  - `/envs`: Dockerfiles for tool-specific sandbox environments
  - `/scripts`: scripts for querying and evaluating LLMs

### Example Usage

#### Verification Tool Setup
To prepare the tool environment for a specific verification language, navigate to the corresponding directory and build the Docker image:
```
cd /envs/<tool_name>
docker build -t <image_name> .
```
Replace `<tool_name>` with the desired verification tool (e.g. FramaC) and `<image_name>` with the corresponding lowercase Docker image name (e.g. framac). Configure any image tags as applicable; these images are invoked by `/scripts/verify.py`. This will set up the sandbox required for running the verifiers.

#### Running Experiments
You need to set up the *API clients* and adjust *resource paths*, *Docker image names*, and *output paths* in the scripts.

To evaluate on VerifyThisBench
```bash
python query_with_feedback.py --tool dafny --attempt 5 --timelimit 60
```

To evaluate on VerifyThisBenchXS
```bash
python query_relaxed_with_feedback.py --attempt 5 --timelimit 60

```
### What's next?
We are working on extending the benchmark to support additional verification tools such as:

- [ ] CBMC  
- [ ] Verus  

Stay tuned for updates and more challenges!

