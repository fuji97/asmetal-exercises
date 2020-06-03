asm MacchinaCaffe

import ../Libs/StandardLibrary

signature:
	enum domain Drink = {COFFE | THE | MILK}
	enum domain CoinType = {HALF | ONE} 
	domain CoinQuantity subsetof Integer
	domain DrinkQuantity subsetof Integer
	dynamic controlled quantity : Drink -> DrinkQuantity
	dynamic controlled totalCoins : CoinQuantity
	dynamic monitored insertedCoin : CoinType

definitions:
	domain CoinQuantity = {0:25}
	domain DrinkQuantity = {0:10}

	rule r_serveDrink ($drink in Drink) =
		if quantity($drink) > 0 then
			par
				totalCoins := totalCoins + 1
				quantity($drink) := quantity($drink ) - 1
			endpar
		endif

	main rule r_Main = 
		if totalCoins < 25 then
			switch insertedCoin
				case HALF:
					r_serveDrink[MILK]	
				case ONE:
					choose $drink in Drink with $drink != MILK and quantity($drink) > 0 do
						r_serveDrink[$drink]
			endswitch
		endif
		
	default init s0:
		function quantity($p in Drink) = 10
		function totalCoins = 0