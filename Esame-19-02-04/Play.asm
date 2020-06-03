asm Play

import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Esame 4/2/19 (laboratorio) ***
//
// REQUISITI:
// Scrivere un modello ASM che implementi il problema descritto qui di seguito.
// L’utente gioca contro il pc.
// Ogni giocatore ha la possibilità di estrarre un numero da 1 a 5. Ad ogni estrazione, vince chi ha estratto il
// numero di valore maggiore, mentre se estraggono lo stesso numero non vince/perde nessuno.
// Ogni giocatore ha inizialmente 5e a disposizione. Se perde, dal suo credito viene scalato 1e e viene aggiunto
// all’avversario. Se estraggono lo stesso numero non viene scalato denaro a nessuno.
// Il gioco continua finchè uno dei due giocatori arriva a 0 Euro.
//
// MODELLO:
// Ad ogni passo di simulazione, il pc e l’utente estraggono un numero. Si possono verificare le seguenti condizioni:
// - Il numero dell’utente è uguale a quello estratto dal pc: partita patta; nessuno perde/guadagna denaro.
// - Il numero dell’utente supera quello estratto dal pc: vince l’utente; l’utente guadagna 1e, il pc perde 1e.
// - Il numero dell’utente è minore di quello estratto dal pc: vince il pc; l’utente perde 1e, il pc guadagna 1e.
// Inizialmente entrambi hanno un credito di 5e ed il gioco continua finchè uno dei due giocatori raggiunge 0e.
// Quando il gioco termina, si vuole sapere chi ha vinto il gioco (WINUSER — WINPC — PATTA) utilizzando
// un’opportuna funzione.
// Utilizzare funzioni detived per winner e finalWinner, oppurtunamente definite, come locazioni per memo-
// rizzare il risultato parziale del gioco e quello totale.
//
// INVARIANTI:
// Scrivere un invariante del modello per garantire che la somma dei crediti dei due giocatori è sempre uguale a 10.
//
// SCENARI:
// Specificare i seguenti due scenari:
// - Se il giocatore seleziona il numero 4 ed il pc sorteggia 2, allora l’utente vince 1 euro.
// - Se il giocatore sorteggia 4 ed il pc sorteggia 5, allora l’utente perde 1 euro ed il pc vince 1 euro.
//
// PROPRIETÀ CTL
// Specificare e verificare tramite AsmetaSMV le seguenti proprietà CTL:
// - il saldo dell’utente può assumere un qualsiasi valore nell’intervallo[0, 10] Euro;
// - nel sistema ci sono sempre 10 Euro;
// - esiste un cammino in cui il saldo del pc è sempre maggiore o uguale a 1 Euro.


signature:
	enum domain Entity = {USER | PC}
	enum domain Winner = {WINUSER | WINPC | PATTA}
	domain Play subsetof Natural
	domain Money subsetof Integer
	dynamic controlled money : Entity -> Money
	dynamic monitored play : Entity -> Play
	dynamic out gameWinner : Winner
	derived winner : Prod(Play, Play) -> Winner
	derived finalWinner : Winner
	
definitions:
	// Inizializzazioni statiche
	domain Play = {1n : 5n}
	domain Money = {0 : 10}
	
	function winner($player in Play, $pc in Play) = 
		if ($player > $pc) then WINUSER
		else if ($pc > $player) then WINPC
		else PATTA
		endif endif
		
	function finalWinner =
		if (money(USER) = 0 and money(PC) != 0) then WINPC
		else if (money(USER) != 0 and money(PC) = 0) then WINUSER
		else PATTA
		endif endif
	
	// Regole
	rule r_Play =
		switch(winner(play(USER), play(PC)))
			case WINUSER:
				par
					money(USER) := money(USER) + 1
					money(PC) := money(PC) - 1
				endpar
			case WINPC:
				par
					money(USER) := money(USER) - 1
					money(PC) := money(PC) + 1
				endpar
		endswitch
	
	// CTL
	// Il valore dei soldi dell'utente può assumere tutti i valori tra 0 e 10
	CTLSPEC(
		ef(money(USER) = 0) and
		ef(money(USER) = 1) and
		ef(money(USER) = 2) and
		ef(money(USER) = 3) and
		ef(money(USER) = 4) and
		ef(money(USER) = 5) and
		ef(money(USER) = 6) and
		ef(money(USER) = 7) and
		ef(money(USER) = 8) and
		ef(money(USER) = 9) and
		ef(money(USER) = 10)
	)
	// Il valore dei soldi dell'utente è sempre tra 0 e 10
	CTLSPEC(ag(money(USER) >= 0 and money(USER) <= 10))
	CTLSPEC(ag(money(USER) + money(PC) = 10))
	CTLSPEC(ef(ag(money(PC) > 1)))
	
	// Invarianti
	invariant over money : money(PC) + money(USER) = 10
		
	// Main rule
	main rule r_Main =
		if (finalWinner != PATTA) then
			gameWinner := finalWinner
		else
			r_Play[]
		endif
	
	default init s0:
		// Inizializzazioni dinamiche
		function money($e in Entity) = 5