use machine::simtx::{Warp, Path, scheduler::SimtxScheduler};
use std::collections::HashMap;

#[derive(Clone)]
pub struct Scheduler;

impl SimtxScheduler for Scheduler {
    fn schedule(simulator:&mut Warp<Self>) -> Option<usize> {

        // threshold for "re-schedule"
        let schedule_trigger = 16;

        if simulator.paths.is_empty() { 
            simulator.current_path = None;//0xFFFFFFFF;
            simulator.cycles_since_last_schedule = schedule_trigger;
            None
        } else {

            // old_pc is:
            // - None if we destroyed the last path
            // - Some(x) if we still have the last path, in order to retrieve it
            //      after fusion
            let old_pc = simulator
                .current_path
                .map(|pid| simulator.paths[pid].fetch_pc);

            // Fusion of path with the same PC
            let mut fused = HashMap::new();
            let mut fusion = false;
            for p in &simulator.paths {
                if let Some(lhs) = fused.get_mut(&p.fetch_pc) {
                    *lhs |= p.execution_mask;
                    fusion = true;
                } else {
                    fused.insert(p.fetch_pc, p.execution_mask);
                }
            }

            // If fusion occurred, rebuild the path table
            // + reset current_path to the good path
            if fusion {
                simulator.fusions += 1;
                let mut npaths = Vec::new();
                for (k, v) in fused {
                    if let Some(pc) = old_pc {
                        if k == pc {
                            simulator.current_path = Some(npaths.len());
                        }
                    }
                    npaths.push(Path::from_pc_mask(k, v));
                }
                simulator.paths = npaths;
            }

            // only schedule if we passed the "schedule threshold" or if the last
            // path we scheduled just died
            if !(simulator.cycles_since_last_schedule >= schedule_trigger
                || old_pc.is_none())
            {
                simulator.cycles_since_last_schedule += 1;
                return simulator.current_path
            }

            // when re-scheduling, reset the cycle counter
            simulator.cycles_since_last_schedule = 0;

            // gather threads which reached the idle threshold
            let idle_threshold = 4;
            let mut too_idle = Vec::new();
            for i in 0..simulator.paths.len() {
                if simulator.paths[i].time_since_scheduled > idle_threshold {
                    too_idle.push(i);
                }
            }

            // work_on represents the list of every path which are eligible for
            // scheduling
            //
            // if we have idle threads, work_on represent only those idle threads
            // if we don't, we just iterate over all threads
            let work_on = if too_idle.is_empty() { (0..simulator.paths.len()).collect() } else { too_idle };
            let work_on : Vec<usize> = work_on.into_iter().filter(|i| {
                simulator.paths[*i].fetch_pc != 0
            }).collect();
            simulator.current_path = Some(work_on[0]);

            // [min pc] over only eligible threads
            for i in work_on {
                // compute the path with the minimum pc
                let ipc = simulator.paths[i].fetch_pc;
                if ipc < simulator.paths[simulator.current_path.unwrap()].fetch_pc {
                    simulator.current_path = Some(i)
                }
            }

            // for each not-chosen path, increment their idle time
            for i in 0..simulator.paths.len() {
                if i == simulator.current_path.unwrap() { simulator.paths[i].time_since_scheduled = 0 }
                else { simulator.paths[i].time_since_scheduled += 1 }
            }

            simulator.current_path
        }
    }
}
