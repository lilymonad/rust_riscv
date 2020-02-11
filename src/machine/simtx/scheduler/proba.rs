use machine::simtx::{Warp, Path, scheduler::SimtxScheduler};
use std::cmp::Reverse;

static WINDOW_SIZE : f32 = 256.;

#[derive(Clone, Default, Debug)]
struct TimeSlice {
    path:usize,
    cycles:usize,
}

impl TimeSlice {
    fn new() -> TimeSlice { TimeSlice::default() }
}

#[derive(Clone)]
pub struct SchedulerData {
    fetch_window:Vec<TimeSlice>,
    window_location:usize,
}

impl Default for SchedulerData {
    fn default() -> SchedulerData { SchedulerData::new() }
}

impl SchedulerData {
    pub fn new() -> SchedulerData {
        SchedulerData { fetch_window:Vec::new(), window_location:0 }
    }

    fn probas(ps:&Vec<Path>) -> Vec<(usize,f32)> {
        let mut with_id : Vec<(usize, Path)> = ps.into_iter()
            .cloned()
            .enumerate()
            .collect();

        // Sort by min-pc
        with_id.sort_unstable_by_key(|(_,p)| Reverse(p.fetch_pc));

        with_id.into_iter()
            .map(|(i,_)| {
                (i, 1. / (2f32).powi(i as i32))
            })
            .collect()
    }
}

impl SimtxScheduler for SchedulerData {

    fn next_path_to_fetch_id(warp:&mut Warp<Self>) -> Option<usize> {
        let sd = &mut warp.scheduler_data;

        let l = sd.fetch_window.len();

        // no path to fetch, nothing to execute on warp
        if l <= 0 { return None }

        // find next path with cycles to execute (from the fetch barrel)
        let mut clock = 0;
        while sd.fetch_window[sd.window_location].cycles <= 0 {
            sd.window_location =  (sd.window_location + 1) % l;
            clock += 1;
            if clock == l {
                warp.trigger_schedule();
                return None
            }
        }

        // advance current path of 1 cycle, and return its id
        sd.fetch_window[sd.window_location].cycles -= 1;
        Some(sd.fetch_window[sd.window_location].path)
    }

    fn schedule(warp:&mut Warp<Self>) {
        let sd = &mut warp.scheduler_data;
        if warp.must_schedule {
            // Get the probability list and sort it by decreasing probability
            let probas = SchedulerData::probas(&warp.paths);

            // Share cycles for each path given their runtime probability
            let mut probas : Vec<(usize, usize)> = probas
                .into_iter()
                .map(|(i,p)| (i, 1 + (p * WINDOW_SIZE) as usize))
                .collect();
            probas.sort_unstable_by_key(|(_,p)| Reverse(p.clone()));

            let l = probas.len();
            let off = sd.window_location;

            // clear the fetch_window, and re-populate it with as many timeslices
            // as there are paths
            sd.fetch_window.clear();
            sd.fetch_window.resize(l, TimeSlice::new());
            probas
                .into_iter()
                .enumerate()
                .for_each(|(j, (i, n))| {
                    sd.fetch_window[(off + j)%l] = TimeSlice { path:i, cycles:n }
                });

            // relocate the window pointer
            sd.window_location = sd.window_location % l;
            warp.must_schedule = false;
        }
    }
}
