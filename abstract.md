This work formalizes the work of Jan Elffers and Mathijs de Weerdt in
[\[1\]](#ref-elffers2017twolengths). Non-preemptive scheduling of jobs with release times and
deadlines on a single machine, $1 \mid r_j \mid L_{\max}$, is polynomial-time solvable
when all jobs have the same length, and when the jobs have two lengths of which the
shorter is $1$. Elffers and de Weerdt settle the remaining case: for every fixed pair of
integer job lengths $p > q > 1$, the problem restricted to the job lengths $\{p, q\}$ is
NP-complete. The reduction produces only numbers polynomial in the
size of the input, which is why they call the problem strongly NP-complete; this
submission proves that bound but states the theorem for the binary encoding.

The proof passes through an auxiliary problem $\mathrm{AUX}(p, q)$ in which some jobs
carry an early and a late deadline and are connected in pairs, of which at least one job
must meet its early deadline. Satisfiability reduces to the auxiliary problem by laying
out, for every literal, a section of blocks of jobs with deadlines close to each other,
in which a truth value appears as one unit of delay. The auxiliary problem reduces to
scheduling on the lengths $\{p, q\}$ by replacing every connected pair with four jobs
whose availability intervals are nested, together with a pinned separator job.

Both constructions are given explicitly, with numbered jobs, and their correctness is
stated separately from their running time. Hardness is stated against the class NP of the
archive and rests on its proof of the Cook–Levin theorem. That integer start times
suffice, which the source remarks in passing, is a statement of its own.