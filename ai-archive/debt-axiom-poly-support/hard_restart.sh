#!/bin/bash
H=$HOME/.isabelle/Isabelle2025-2
ps -eo pid,comm,args --no-headers | awk '($2=="python3" && $0 ~ /run_probe/) || ($2=="poly") || ($2=="bash" && $0 ~ /repl_server/) {print $1}' > /tmp/kl.txt
echo "killing: $(tr '\n' ' ' < /tmp/kl.txt)"
for p in $(cat /tmp/kl.txt); do kill "$p" 2>/dev/null; done
sleep 4
for p in $(cat /tmp/kl.txt); do kill -9 "$p" 2>/dev/null; done
sleep 2
echo "poly left: $(ps -eo comm --no-headers | grep -c '^poly$')   port: $((ss -ltn 2>/dev/null||netstat -ltn) | grep -c 6669)"
[ -d "$H/event_log" ] && mv "$H/event_log" "$H/event_log.$(date +%m%d_%H%M%S)"
rm -f "$H/guard_race.tsv" "$H/guard_race.tsv.goals" "$H/guess_inst_probe.tsv" "$H/proof_store_probe.log"
nohup setsid "$HOME/start_repl.sh" > "$HOME/repl_fresh.log" 2>&1 < /dev/null &
for i in $(seq 1 360); do (ss -ltn 2>/dev/null || netstat -ltn) | grep -q 6669 && { echo "REPL up (~$((i*10))s)"; break; }; sleep 10; done
(ss -ltn 2>/dev/null || netstat -ltn) | grep -q 6669 || { echo "REPL NOT up"; grep -n "\*\*\*" "$HOME/repl_fresh.log" | head -8; exit 1; }
nohup setsid python3 "$HOME/run_probe.py" > "$HOME/exp2_baseline_driver.log" 2>&1 < /dev/null &
sleep 2; echo "driver: $(pgrep -f run_probe.py | head -1)"
