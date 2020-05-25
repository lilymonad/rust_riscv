{
    for i in self.warps[wid].alive_cores_ids() {
        let core = &mut self.warps[wid].cores[i];
        let mut str_addr = core.registers[10];
        let mut to_parse = String::new();
        let mut byte = mem.get_8(str_addr as usize);

        //println!("byte at 0x{:x}", str_addr);

        while byte != 0 && byte != ('\n' as u8) {
            to_parse.push(byte as char);
            str_addr += 1;
            byte = mem.get_8(str_addr as usize);
        }

        //println!("strtof({})", to_parse);
        let parsed = to_parse.parse()
            .expect(format!("couldnt parse {} to float", to_parse).as_str());
        //println!("strtof(\"{}\") = {}", to_parse, parsed);

        let x : MachineF32 = MachineF32::from_f32(parsed);
        unsafe { core.set_ri(10, x.bits.lo as i32); }
    }
    self.warps[wid].advance_pc(pathid, advance);
}
