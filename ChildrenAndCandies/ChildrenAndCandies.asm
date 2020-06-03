asm ChildrenAndCandies
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Bambini e Caramelle ***
//
// Modellare in AsmetaL il seguente problema: 
// Ci sono 6 bambini seduti a tavola in cerchio. All'inizio ogni bambino ha 4 caramelle. 
// Ad ogni passo di simulazione, la macchina sceglie un bambino a caso che esegue una delle seguenti mosse:
// 1. se ha almeno una caramella, ne mangia una;
// 2. se non ha alcuna caramella:
// 2.1 se il suo vicino a destra ha almeno una caramella, ne ruba una ma non la mangia immediatamente;
// 2.2 se il suo vicino a destra non ha alcuna caramella, controlla il vicino a sinistra: se questo ha
//     almeno una caramella, ne ruba una e la da al suo vicino di destra.

signature:
	domain Child subsetof Agent
	domain Candy subsetof Integer
	
	dynamic controlled candies : Child -> Candy
	//dynamic controlled selectedChild : Child
	
	derived hasCandies : Child -> Boolean
	derived noCandyLeft : Boolean
	
	static left : Child -> Child
	static right : Child -> Child
	
	static child1 : Child
	static child2 : Child
	static child3 : Child

definitions:
	// Inizializzazioni
	domain Candy = {0 : 12}
	
	function left($child in Child) = switch $child
			case child1 : child3
			case child2 : child1
			case child3 : child2
		endswitch
		function right($child in Child) = switch $child
			case child1 : child2
			case child2 : child3
			case child3 : child1
		endswitch
	
	function hasCandies($child in Child) = candies($child) > 0
	
	function noCandyLeft = not(exist $child in Child with hasCandies($child))

	// Regole
	rule r_EatCandy($child in Child) = candies($child) := candies($child) - 1
	
	rule r_StealCandy($from in Child, $to in Child) = par
		candies($from) := candies($from) - 1
		candies($to) := candies($to) + 1
	endpar
	
	rule r_Child =
		if (candies(self) > 0) then
			r_EatCandy[self]
		else if (hasCandies(right(self))) then
			r_EatCandy[right(self)]
		else if (hasCandies(left(self))) then
			r_StealCandy[left(self), right(self)]
		endif endif endif
	
	// Invarianti
	invariant over candies : not (exist $child in Child with candies($child) < 0)
	
	// CTL
	CTLSPEC(ag(ef(noCandyLeft)))
	
	// Main Rule
	main rule r_Main = 
		choose $child in Child with true do par
			program($child)
			skip
			//selectedChild := $child
		endpar
	
	// Default Init
	default init s0:
		function candies($child in Child) = 4
	
	// Agenti
	agent Child : r_Child[]
