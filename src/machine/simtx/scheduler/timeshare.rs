use machine::simtx::{MAX_TPW, Warp, Path, scheduler::SimtxScheduler};

#[derive(Clone, Default)]
pub struct Scheduler {
    slices:[usize;MAX_TPW],
    pointer:usize,
}

impl SimtxScheduler for Scheduler {
    fn schedule(simulator:&mut Warp<Self>) -> Option<usize> {

        //
        // This is a first attempt
        // It will be improved later, using better scheduling heuristics
        // For now, let's try to implement a simple function 
        // Vec<Path> -> Vec<(usize, TimeSlice)>
        // implementing LexicoScheduler
        //

        let mut clock = 0;
        let mut path = loop {
            let pointer = simulator.scheduler.pointer;
            let remaining = &mut simulator.scheduler.slices[pointer];
            if *remaining != 0 {
                *remaining -= 1;
                break Some(pointer)
            }
            simulator.scheduler.pointer = (pointer + 1) % MAX_TPW;
            clock += 1;
            if clock == MAX_TPW { break None }
        };

        // If there are no more path to run
        if path.is_none() || simulator.schedule_invalidated {

            // Compute a new time share
            let mut paths : Vec<(usize, Path)> = simulator.paths.iter()
                .cloned()
                .enumerate()
                .collect();
            paths.sort_by_key(|(_, p)| p.fetch_pc);

            let mut decreasing = 1f32;
            let pool_size = 512f32;
            let mut pool = pool_size as usize;
            let probas : Vec<(usize, f32)> = paths.iter()
                .map(|(i,_)| { decreasing /= 2f32; (*i, decreasing) })
                .collect();

            for s in &mut simulator.scheduler.slices {
                *s = 0;
            }

            let mut x = -1;
            for (i, p) in &probas {
                let n = (p * pool_size) as usize;
                pool -= n;
                x = *i as i32;
                simulator.scheduler.slices[*i] = n; 
            }

            if x >= 0 {
                simulator.scheduler.slices[x as usize] += pool;
            }

            // Re-search for a new path
            clock = 0;
            path = loop {
                let pointer = simulator.scheduler.pointer;
                let remaining = &mut simulator.scheduler.slices[pointer];
                if *remaining != 0 {
                    *remaining -= 1;
                    break Some(pointer)
                }
                simulator.scheduler.pointer = (pointer + 1) % MAX_TPW;
                clock += 1;
                if clock == MAX_TPW { break None }
            };
            simulator.schedule_invalidated = false;
        }

        // Update the path (found or not) and return it
        simulator.current_path = path;
        path
    }
}
