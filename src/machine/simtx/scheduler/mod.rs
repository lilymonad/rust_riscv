use machine::simtx::Warp;

mod lexico;
pub use machine::simtx::scheduler::lexico::Scheduler as LexicoScheduler;

//mod proba;
//pub use proba::Scheduler as ProbaScheduler;

pub trait SimtxScheduler : Sized + Clone {
    fn schedule(simulator:&mut Warp<Self>) -> Option<usize>;
}
