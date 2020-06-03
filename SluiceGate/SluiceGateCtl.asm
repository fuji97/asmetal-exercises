asm SluiceGateCtl
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** SluiceGate ***
//
// - Sistema di irrigazione che controlla il flusso dell'acqua tramite una chiusa la chiusa è sbarrata
//   da una saracinesca che si può alzare ed abbassare
// - La saracinesca deve essere totalmente aperta per 10 minuti ogni tre ore; nel resto
//   del tempo deve essere totalmente chiusa. dei sensori segnalano se è completamente chiusa 
//   o completamente aperta.
// - La saracinesca viene aperta/chiusa ruotando delle viti che sono manovrate da un motore.
// - Al motore vengono inviati 4 segnali:
//   - per ruotare le viti in senso orario,
//   - per ruotarle in senso antiorario,
//   - per accenderlo e
//   - per spegnerlo
// - Il computer controlla il sistema emettendo i quattro segnali per guidare il motore;
// - Il computer è collegato ai due sensori posti alla estremità del percorso della saracinesca per conoscerne la posizione.
//
// Livello 2: SluiceGateCtl (multi-agente)
// - Si introduce un agente per il sistema di controllo ed un agente per l’ambiente

signature:
	domain Minutes subsetof Integer
	abstract domain Position
	domain PulseCtl subsetof Agent
	domain SluiceGateCtl subsetof Agent
	enum domain Phase = {FULLYCLOSED | FULLYOPEN | OPENING | CLOSING}
	enum domain Direction = {CLOCKWISE | ANTICLOCKWISE}
	enum domain MotorState = {ON | OFF}
	dynamic controlled phase : Phase
	dynamic controlled direction : Direction
	dynamic controlled motor : MotorState
	dynamic controlled pulse : Direction -> Boolean
	dynamic controlled pulse : MotorState -> Boolean
	dynamic monitored passed : Minutes -> Boolean
	dynamic monitored event : Position -> Boolean
	
	static openPeriod : Minutes
	static closedPeriod : Minutes
	static top : Position
	static bottom : Position
	static pulseCtl : PulseCtl
	static sluiceGateCtl : SluiceGateCtl
	
definitions:
	// Inizializzazioni statiche
	domain Minutes = {10, 170}
	function openPeriod = 10
	function closedPeriod = 170
	
	// Regole
	rule r_Open = par
		phase := OPENING
		pulse(ANTICLOCKWISE) := true
		pulse(ON) := true
	endpar
	
	rule r_Close = par
		phase := CLOSING
		pulse(CLOCKWISE) := true
		pulse(ON) := true
	endpar
	
	rule r_Opened = par
		phase := FULLYOPEN
		pulse(OFF) := true
	endpar
	
	rule r_Closed = par
		phase := FULLYCLOSED
		pulse(OFF) := true
	endpar
	
	rule r_PulseCtl = par
		if (pulse(CLOCKWISE)) then par
			direction := CLOCKWISE
			pulse(CLOCKWISE) := false
		endpar endif
		if (pulse(ANTICLOCKWISE)) then par
			direction := ANTICLOCKWISE
			pulse(ANTICLOCKWISE) := false
		endpar endif
		if (pulse(ON)) then par
			motor := ON
			pulse(ON) := false
		endpar endif
		if (pulse(OFF)) then par
			motor := OFF
			pulse(OFF) := false
		endpar endif
	endpar
	
	rule r_SluiceGateCtl = par
		if (phase = FULLYOPEN and passed(openPeriod)) then
			r_Close[]
		endif
		if (phase = FULLYCLOSED and passed(closedPeriod)) then
			r_Open[]
		endif
		if (phase = OPENING and event(top)) then
			r_Opened[]
		endif
		if (phase = CLOSING and event(bottom)) then
			r_Closed[]
		endif
	endpar
	
	// CTL
	CTLSPEC ag((phase = FULLYCLOSED and passed(170)) implies af(pulse(ON) and pulse(ANTICLOCKWISE)))
	CTLSPEC ag((phase = FULLYOPEN and passed(10)) implies af(pulse(ON) and pulse(CLOCKWISE)))
	CTLSPEC ag((phase = OPENING and event(top)) implies af(pulse(OFF)))
	CTLSPEC ag((phase = CLOSING and event(bottom)) implies af(pulse(OFF)))
	
	// Invarianti
	invariant over pulse(MotorState) : not(pulse(ON) and pulse(OFF))
	invariant over pulse(Direction) : not(pulse(CLOCKWISE) and pulse(ANTICLOCKWISE))
	
	
	// Main Rule
	main rule r_Main = par
		program(sluiceGateCtl)
		program(pulseCtl)
	endpar
	
default init s0:
	// Inizializzazioni dinamiche
	function phase = FULLYCLOSED
	function motor = OFF
	function direction = CLOCKWISE
	function pulse($dir in Direction) = false
	function pulse($motor in MotorState) = false
	
	// Agenti
	agent SluiceGateCtl : r_SluiceGateCtl[]
	agent PulseCtl : r_PulseCtl[]