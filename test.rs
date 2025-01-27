fn foo() {
    match state {
        RunState::Global_factorial => {
            let _ = "bineq, a0, 0, _recurse";
            if a0.i32() != Register::from_i(0isize).i32() {
                state = Local__recurse;
                continue 'run_loop;
            }
            let _ = "mov, r0, 1";
            t0 = Register::from_i(1isize);
            let _ = "ret";
            let op = pop!();
            state = RunState::from_u(op.u())?;
            continue 'run_loop;
        }
        RunState::Local__recurse => {
            let _ = "push, a0";
            push!(a0);
            let _ = "subi, a0, a0, 1";
            *a0.i32_mut() =
                Register::from_i32(a0.i32().wrapping_sub(Register::from_i(1isize).i32()));
            push!(Register::from_u(RunState::return_0 as usize));
            let _ = "call, factorial";
            state = Global_factorial;
            continue 'run_loop;
        }
        RunState::return_0 => {
            let _ = "pop, a0";
            *a0.i_mut() = pop!();
            let _ = "muli, r0, r0, a0";
            *t0.i32_mut() = Register::from_i32(t0.i32().wrapping_mul(a0.i32()));
            let _ = "ret";
            let op = pop!();
            state = RunState::from_u(op.u())?;
            continue 'run_loop;
        }
    }
}
