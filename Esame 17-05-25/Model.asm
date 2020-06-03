asm Model
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Esame 25/5/17 (laboratorio) ***
//
// MODELLO:
// Scrivere un modello AsmetaL che implementi il problema descritto qui di seguito.
// Ci sono 3 giocatori attorno ad un tavolo. Inizialmente ogni giocatore ha 3 token.
// Ad ogni passo di simulazione, la macchina sceglie un giocatore a caso che esegue
// una delle seguenti mosse:
// 1. se ha almeno un token, ne mette uno nel piatto;
// 2. se non ha alcun token:
//   a) se il suo vicino a destra ha almeno un token, ne prende uno (ma non usa a
//      quel giro);
//   b) se il suo vicino a destra non ha alcun token, controlla il vicino a sinistra: se
//      questo ha almeno un token, ne passa uno al suo vicino di destra.
//
// INVARIANTI:
// Scrivere un invariante del modello per garantire che la somma dei token dei giocatori
// e del piatto è sempre uguale a 9.
//
// PROPRIETÀ CTL:
// Specificare e verificare tramite AsmetaSMV le seguenti proprietà CTL:
// - nel sistema ci sono sempre al massimo 9 token;
// - ogni giocatore non ha mai più di 3 token;
// - prima o poi nessun giocatore ha token;
// - prima o poi il piatto ha 9 token.

signature:
	abstract domain Player
	domain Token subsetof Integer
	dynamic controlled token : Player -> Token
	dynamic controlled left : Player -> Player
	dynamic controlled right : Player -> Player
	dynamic controlled plate : Token
	dynamic controlled currentPlayer : Player
	
	derived hasTokens : Player -> Boolean
	derived totalTokens : Token
	
	static player1 : Player
	static player2 : Player
	static player3 : Player
	
definitions:
	// Inizializzazioni statiche
	domain Token = {0 : 9}
	
	function hasTokens( $player in Player) = token( $player ) > 0
	
	function totalTokens = token(player1) + token(player2) + token(player3) + plate
	
	// Regole
	rule r_GiveToPlate($player in Player) = par
		token($player) := token($player) - 1
		plate := plate + 1
	endpar
	
	rule r_GiveToPlayer($from in Player, $to in Player) = par
		token($from) := token($from) - 1
		token($to) := token($to) + 1
	endpar
	
	rule r_Player($player in Player) =
		if (hasTokens( $player )) then
			r_GiveToPlate [$player]
		else if (hasTokens(right( $player ))) then
			r_GiveToPlayer [right( $player ), $player]
		else if (hasTokens(left($player))) then
			r_GiveToPlayer[left($player), right($player)]
		endif endif endif
	
	// CTL
	CTLSPEC(ag(totalTokens <= 10))
	CTLSPEC(ag(token(player1) <= 3 and token(player2) <= 3 and token(player3) <=3))
	CTLSPEC(ag(ef(token(player1) = 0 and token(player2) = 0 and token(player3) = 0)))
	CTLSPEC(ag(ef(plate = 9)))
	
	// Invarianti
	invariant over token, plate : totalTokens = 9
	
	// Main Rule
	main rule r_Main =
		choose $player in Player with true do par
			currentPlayer := $player
			r_Player[$player]
		endpar
	
default init s0:
	// Inizializzazioni dinamiche
	function token($player in Player) = 3
	function plate = 0
	function left($player in Player) = switch $player
		case player1 : player3
		case player2 : player1
		case player3 : player2
	endswitch
	function right($player in Player) = switch $player
		case player1 : player2
		case player2 : player3
		case player3 : player1
	endswitch
	
	// Agenti
	