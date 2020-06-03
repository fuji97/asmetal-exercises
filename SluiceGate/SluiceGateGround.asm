asm SluiceGateGround
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
// Livello 0: SluiceGateGround (ground model)
// - Saracinesca solo in posizione di totale apertura o totale chiusura
// - Non modellato il movimento di apertura/chiusura
// - Non modellato il motore
// - Si considera solo il trascorrere degli intervalli di tempo in cui la saracinesca deve rimanere aperta/chiusa

signature:
	domain Minutes subsetof Integer
	enum domain Phase = {FULLYCLOSED | FULLYOPEN}
	dynamic controlled phase : Phase
	dynamic monitored passed : Minutes -> Boolean
	
definitions:
	// Inizializzazioni statiche
	domain Minutes = {10, 170}
	
	// Regole
	rule r_Open = phase := FULLYOPEN
	
	rule r_Close = phase := FULLYCLOSED
	
	// CTL
	CTLSPEC ag((phase = FULLYCLOSED and passed(170)) implies ax(phase = FULLYOPEN))
	CTLSPEC ag((phase = FULLYOPEN and passed(10)) implies ax(phase = FULLYCLOSED))
	
	// Invarianti
	
	
	// Main Rule
	main rule r_main = par
		if (phase = FULLYOPEN and passed(10)) then
			r_Close[]
		endif
		if (phase = FULLYCLOSED and passed(170)) then
			r_Open[]
		endif
	endpar
	
default init s0:
	// Inizializzazioni dinamiche
	function phase = FULLYCLOSED
	
	// Agenti
	