asm SluiceGateMotorCtl
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
// Livello 1: SluiceGateMotorCtl (mono agente)
// - Si introducono il motore ed i sensori di posizione della saracinesca

signature:
	domain Minutes subsetof Integer
	abstract domain Position
	enum domain Phase = {FULLYCLOSED | FULLYOPEN | OPENING | CLOSING}
	enum domain Direction = {CLOCKWISE | ANTICLOCKWISE}
	enum domain MotorState = {ON | OFF}
	dynamic controlled phase : Phase
	dynamic controlled direction : Direction
	dynamic controlled motor : MotorState
	dynamic monitored passed : Minutes -> Boolean
	dynamic monitored event : Position -> Boolean
	
	static openPeriod : Minutes
	static closedPeriod : Minutes
	static top : Position
	static bottom : Position
	
definitions:
	// Inizializzazioni statiche
	domain Minutes = {10, 170}
	function openPeriod = 10
	function closedPeriod = 170
	
	// Regole
	rule r_Open = par
		phase := OPENING
		direction := ANTICLOCKWISE
		motor := ON
	endpar
	
	rule r_Close = par
		phase := CLOSING
		direction := CLOCKWISE
		motor := ON
	endpar
	
	rule r_Opened = par
		phase := FULLYOPEN
		motor := OFF
	endpar
	
	rule r_Closed = par
		phase := FULLYCLOSED
		motor := OFF
	endpar
	
	// CTL
	CTLSPEC ag((phase = FULLYCLOSED and passed(170)) implies ex(a(phase = OPENING, phase = FULLYOPEN)))
	CTLSPEC ag((phase = FULLYOPEN and passed(10)) implies ex(a(phase = CLOSING, phase = FULLYCLOSED)))
	
	// Invarianti
	invariant over phase, motor : (phase = FULLYOPEN or phase = FULLYCLOSED) xor motor = ON
	invariant over phase, motor : (phase = OPENING or phase = CLOSING) xor motor = OFF
	
	
	// Main Rule
	main rule r_main = par
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
	
default init s0:
	// Inizializzazioni dinamiche
	function phase = FULLYCLOSED
	function motor = OFF
	function direction = CLOCKWISE
	
	// Agenti
	