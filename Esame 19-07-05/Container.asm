asm Container
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Esame del 5 Luglio 2019 (Laboratorio) ***
//
// REQUISITI
// Scrivere una specifica che modelli il funzionamento di un magazzino di container utilizzibali per stivare merce.
// Il magazzino ha 25 container disposti a 5 per fila e ciascuno numerato da una coppia di valori (i,j) con i
// relativo alla riga in cui è parcheggiato il container, e j la colonna. In ogni momento è possibile selezionare un
// container libero per stivare la merce.
// I container occupati da merce vengono vuotati secondo una politica descritta sotto.
//
// MODELLO ASMETAL
// Ad ogni passo di simulazione:
// • l’utente seleziona un container vuoto da poter riempire;
// • tutti i container occupati vengono vuotati con probabilità del 10% se si trovano sulla prima riga, del 20%
// se si trovano sulla seconda riga, del 30% se si trovano sulla terza riga, del 40% se si trovano in quarta fila
// e del 50% se si trovano in quinta fila.
// All’inizio tutti i container sono liberi.
//
// SCENARI
// Specificare in Avalla uno scenario che riproduca la seguente situazione: tutti i container sono occupati tranne
// quello di posto (2,3), questo viene selezionato per essere riempito e il suo stato diventa occupato.
// Specificare un secondo scenario a scelta che mostri l’ adeguatezza del modello rispetto ai requisiti.
//
// PROPRIETÀ CTL
// Specificare tramite AsmetaSMV una proprietà temporale che verifichi che:
// • esiste uno stato in cui tutti i contanier sono occupati;
// • esiste uno stato a partire dal quale inizia un cammino in cui tutti i container sono occupati.
// Trovare tramite model checking un cammino che porti in uno stato in cui i container (1,2) e (1,5) sono occupati.

signature:
	enum domain State = {FULL | EMPTY}
	domain Row subsetof Integer
	domain Column subsetof Integer
	domain Probability subsetof Integer
	dynamic controlled container : Prod(Row, Column) -> State
	dynamic monitored fillRow : Row
	dynamic monitored fillColumn : Column
	
	derived isFull : Boolean
	
	static probability : Row -> Probability
	
definitions:
	// Inizializzazioni statiche
	domain Row = {1 : 5}
	domain Column = {1 : 5}
	domain Probability = {0 : 10}
	
	function probability($row in Row) = switch $row
		case 1 : 1
		case 2 : 2
		case 3 : 3
		case 4 : 4
		case 5 : 5
	endswitch
	
	function isFull = (forall $row in Row, $col in Column with container($row, $col) = FULL)
	
	// Regole
	rule r_FillContainer($row in Row, $col in Column) = 
		if (container($row, $col) = EMPTY) then
			container($row, $col) := FULL
		endif
		
	rule r_EmptyContainer($row in Row, $col in Column) =
		if (container($row, $col) = FULL) then
			container($row, $col) := EMPTY
		endif
		
	rule r_EmptyProbability($row in Row, $col in Column) = 
		choose $i in Probability with true do
			if ($i < probability($row)) then
				r_EmptyContainer[$row, $col]
			endif
		
	rule r_EmptyPhase =
		forall $row in Row, $col in Column with true do
			r_EmptyProbability[$row, $col]
	
	// CTLSPEC
	CTLSPEC(ef(isFull))		// Esiste uno stato in cui tutti i contanier sono occupati;
	CTLSPEC(ef(eg(isFull)))	// Esiste uno stato a partire dal quale inizia un cammino in cui tutti i container sono occupati.
	
	CTLSPEC(not(ef(container(1,2) = FULL and container(1,5) = FULL)))
	// Trovare tramite model checking un cammino che porti in uno stato in cui i container (1,2) e (1,5) sono occupati
	
	// Invarianti
	
	// Main rule
	main rule r_Main = par
		r_FillContainer[fillRow, fillColumn]
		r_EmptyPhase[]
	endpar
	
	// Inzializzazioni dinamiche
default init s0:
	function container($row in Row, $col in Column) = EMPTY