# c273 kernel check and raw-step counts: how to run

Needs Rocq 8.20.1 with native compilation (opam switch `rocq`), gcc and rustc. Run everything from this folder (`kernel/`):

```sh
./run_all.sh setup               # builds BusyCoq, Rules273, Kernel273, Final273, both counters (a few minutes)
nohup ./run_all.sh jobs 120 > logs/run.out 2>&1 &   # 1,569 tasks: 523 kernel jobs, 523 C counts, 523 Rust counts
./run_all.sh chain               # once every kernel job is done: compiles Chain.v (c273_halts : halts tm c0)
python3 sum_counts.py .          # once every count is done: the exact raw-step total
```

Resumable: a task is done only when its marker in `done/` exists (written after coqc exits 0 and the .vo exists, or after a
count's end state matches the next checkpoint). Rerunning `jobs` skips done tasks. Everything a restore needs is under this folder:
pull `done/ logs/ counts/ jobs/*.vo` (and the setup .vo files) every 10 minutes; to restore on a new box, push the whole
directory back, run `setup` (it skips if done/SETUP.ok and the .vo files are present) and `jobs` again.

Costs measured on an EPYC 9R14 core: kernel jobs about 1,800 s each (7.8e7 map steps/s), about 446 MB RSS each; C counts about
1,000 s, Rust counts about 1,500 s per 2^37-step job. Failures go to `logs/failures.log`.
