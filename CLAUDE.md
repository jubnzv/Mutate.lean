## Usage

### Running with live results
If you're asked to execute the mutation testing NOT in background: start it with Bash `run_in_background` from the target project, then watch the log with Monitor (stdout is flushed per line, so every verdict is an event):
```
cd <project> && lake env lean --run /path/to/Mutate.lean -v File.lean > <log> 2>&1
tail -n +1 -f <log> | grep --line-buffered -E 'killed|survived|stillborn|error|baseline'
```
