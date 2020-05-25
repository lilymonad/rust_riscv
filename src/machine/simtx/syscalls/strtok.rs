{
    let _cid = self.warps[wid].get_single_core_id();
    let core = &mut self.warps[wid].cores[wid];
    let mut addr1 = core.registers[10] as usize;
    let mut addr2 = core.registers[11] as usize;

    unsafe {
        let mut strptr = 0 as * mut c_char;
        let delimptr : * const c_char;
        if addr1 != 0 {
            // deallocate the previously allocated CString
            if STRTOK_VEC != 0 as * mut c_char {
                std::mem::drop(CString::from_raw(STRTOK_VEC));
            }

            // retrieve the new CString
            let mut strvec = Vec::new();
            let mut byte = mem.get_8(addr1 as usize);
            while byte != 0 {
                strvec.push(byte);
                addr1 += 1;
                byte = mem.get_8(addr1 as usize);
            }

            STRTOK_VEC = CString::from_vec_unchecked(strvec).into_raw();
            strptr = STRTOK_VEC;
        }

        // retrieve the new token string
        let mut strvec = Vec::new();
        let mut byte = mem.get_8(addr2 as usize);
        while byte != 0 {
            strvec.push(byte);
            addr2 += 1;
            byte = mem.get_8(addr1 as usize);
        }

        delimptr = CString::from_vec_unchecked(strvec).into_raw()
            as * const c_char;


        let ret = strtok(strptr, delimptr);
        core.registers[10] = ret as i32;
    }

    self.warps[wid].advance_pc(pathid, advance);
}
