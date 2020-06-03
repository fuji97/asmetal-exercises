asm SchedulerSJN

import ../Libs/StandardLibrary

signature:
	dynamic domain Job subsetof Agent
	dynamic domain Scheduler subsetof Agent
	enum domain State = {WAITING | RUNNING | DEAD}
	
	dynamic controlled state: Job -> State
	dynamic controlled cpu: Agent
	dynamic controlled remainingTime: Job -> Integer
	
	static scheduler: Scheduler
	//static job1: Job
	//static job2: Job
	//static job3: Job
	//dynamic controlled jobs: Integer -> Job
	
definitions:
	rule r_Job =
		if (remainingTime(self) > 0) then
			remainingTime(self) := remainingTime(self) - 1
		else
			par
				state(self) := DEAD
				cpu := scheduler
			endpar
		endif
		
	rule r_Scheduler = 
		choose $job in Job with 
		state($job) = WAITING and 
		(forall $p2 in Job with ($job != $p2 and state($p2) = WAITING) implies remainingTime($job) <= remainingTime($p2)) 
		do
			par
				state($job) := RUNNING
				cpu := $job
			endpar
			
	rule r_CreateJob =
		extend Job with $job do par
			state($job) := WAITING
			choose $time in {1 : 10} with true do
				remainingTime($job) := $time
		endpar
		
	// Invariants
	invariant over state: (exist unique $job in Job with state($job) = RUNNING) xor 
							(forall $jobn in Job with state($jobn) != RUNNING)
	invariant over state: (forall $job in Job with state($job) = RUNNING iff (cpu = $job))
	invariant over state: (forall $job in Job with state($job) != RUNNING) iff (cpu = scheduler)
	
	main rule r_Main = par
		program(cpu)
		if (cpu = scheduler) then
			r_CreateJob[]
		endif
	endpar
			
	default init s0:
		//function state($job in Job) = WAITING
		//function remainingTime($job in Job) = switch ($job)
			//case job1: 7
			//case job2: 2
			//case job3: 5
		//endswitch
		function cpu = scheduler
		
	agent Scheduler:
		r_Scheduler[]
		
	agent Job:
		r_Job[]
			