asm Es4
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Esercizio 4 ***
// Il sistema di controllo è costituito da due semafori collegati ad un computer che, per
// ciascuna semaforo, ne determina lo stato VERDE, GIALLO e ROSSO. Il funzionamento dei semafori è
// controllato dal computer in base al seguente ciclo fisso di quattro fasi: fase1, per 30 secondi,
// entrambe i semafori sono in GIALLO; fase2, per 120 secondi un semaforo è in VERDE e l’altro è in
// ROSSO; fase3, per 30 secondi entrambi i semafori sono in GIALLO nuovamente; fase4, per 120
// secondi il semaforo che prima era in VERDE passa da GIALLO a ROSSO mentre l’altro passa da
// GIALLO a VERDE. Ed il ciclo si ripete.
//
// *** Esercizio 5 ***
// Scrivere tre proprietà CTL, una di safety, una di liveness e una di reachability

signature:
	enum domain Phase = {PHASE1 | PHASE2 | PHASE3 | PHASE4}
	enum domain Color = {RED | GREEN | YELLOW}
	domain Time subsetof Integer
	abstract domain Semaphore
	dynamic controlled phase : Phase
	dynamic controlled state : Semaphore -> Color
	dynamic monitored timePassed : Time -> Boolean
	
	static shortTime : Time
	static longTime : Time
	
	static semaphore1 : Semaphore
	static semaphore2 : Semaphore
	
definitions:
	domain Time = {1 : 120}
	function shortTime = 30
	function longTime = 120
	
	rule r_ChangeColor($sem in Semaphore, $color in Color) =
		state($sem) := $color
		
	rule r_Phase1 = par
		phase := PHASE1
		r_ChangeColor[semaphore1, YELLOW]
		r_ChangeColor[semaphore2, YELLOW]
	endpar
	
	rule r_Phase2 = par
		phase := PHASE2
		r_ChangeColor[semaphore1, GREEN]
		r_ChangeColor[semaphore2, RED]
	endpar
	
	rule r_Phase3 = par
		phase := PHASE3
		r_ChangeColor[semaphore1, YELLOW]
		r_ChangeColor[semaphore2, YELLOW]
	endpar
	
	rule r_Phase4 = par
		phase := PHASE4
		r_ChangeColor[semaphore1, RED]
		r_ChangeColor[semaphore2, GREEN]
	endpar
	
	CTLSPEC ag(not(state(semaphore1) = GREEN and state(semaphore2) = GREEN))	// Safety
	CTLSPEC ag(ef(state(semaphore1) = GREEN or state(semaphore2) = GREEN))		// Liveness
	CTLSPEC ef(state(semaphore1) = GREEN)										// Reachability
	CTLSPEC ef(state(semaphore2) = GREEN)										// Reachability
	
	main rule r_Main = par
		if (phase = PHASE1 and timePassed(shortTime)) then
			r_Phase2[]
		endif
		if (phase = PHASE2 and timePassed(longTime)) then
			r_Phase3[]
		endif
		if (phase = PHASE3 and timePassed(shortTime)) then
			r_Phase4[]
		endif
		if (phase = PHASE4 and timePassed(longTime)) then
			r_Phase1[]
		endif
	endpar	
	
default init s0:
	function phase = PHASE1
	function state($state in Semaphore) = YELLOW

	