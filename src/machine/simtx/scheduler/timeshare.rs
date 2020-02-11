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

        // Try to get the next path to run
        let mut path = None;
        for _ in 0..MAX_TPW {
            let pointer = simulator.scheduler.pointer;
            if simulator.scheduler.slices[pointer] != 0 {
                path = Some(pointer);
                break
            }
            simulator.scheduler.pointer = (pointer + 1) % MAX_TPW;
        }

        // If there are no more path to run
        if path.is_none() {

            // Compute a new time share
            let mut paths : Vec<(usize, Path)> = simulator.paths.iter()
                .cloned()
                .enumerate()
                .collect();
            paths.sort_by_key(|(_, p)| p.fetch_pc);

            let mut decreasing = 1f32;
            let probas : Vec<(usize, f32)> = paths.iter()
                .map(|(i,_)| { decreasing /= 2f32; (*i, decreasing) })
                .collect();

            for (i, p) in probas {
                simulator.scheduler.slices[i] = (p * 256f32) as usize; 
            }

            // Re-search for a new path
            path = None;
            for _ in 0..MAX_TPW {
                let pointer = simulator.scheduler.pointer;
                if simulator.scheduler.slices[pointer] != 0 {
                    path = Some(pointer);
                    break
                }
                simulator.scheduler.pointer = (pointer + 1) % MAX_TPW;
            }
        }

        // Update the path (found or not) and return it
        simulator.current_path = path;
        path
    }
}
