# Lambing intepreter

## Składnia języka
Laming jest typowym przykładem prostego języka imperatywnego. Wyposażony jest w:
- funkcje różnych typów (w tym void) o dowolnej liczbie parametrów typów int, bool, string, list<> lub referencji na te typy.
- analogicznie zmienne podanych typów
- deklaracja zmiennych może odbywać się z przypisaniem wartości lub bez
- blok deklaracji jest spójny i w funkcji (w tym w main!) musi być przed blokiem stmt
- main! oraz funkcje posiadają lokalne zmienne
- deklaracje przed main! są globalne
- print służy do wypisywania zmiennej, wyrażenie i t.d. w nowej linii
- listy posiadają metody 
	* .new(wartość) - dodaje nowy element (sgodny z typem listy) na koniec
	* .size()
	* .clear()
	* .delete(i) - usuwa element na pozycji i (i = 0, 1, ...)
	* [i] - wartość na pozycji i
- nie wolno nadpisywać zmiennych globalnych (w tym nie mogą tak się nazywać parametry funkcji)
- można natomiast przy wejściu do np funkcji nadpisać poprzednie zmienne lokalne (w tym zmieniając ich typ)

## Jak urochomić

```
bnfc lambing.cf
make
./interpreter good/goodXX.lb > good/outXX.txt 2> good/errXX.txt
./interpreter bad/badXX.lb 2> bad/errXX.txt
```

W plikach goodXX.lb są programy:
1 - kilka zmiennych globalnych, funkcje void oraz int, przypisanie funkcji na zmienna, wywolanie funkcji void z main!, kilka zmiennych lokalnych oraz print
2 - porównywanie na równość zmiennych trzech typów, nierówności intów, while
3 - wszystkie możliwe wersje if
4 - rekurencyjna funkcja
5 - funkcja z zagnieżdżoną deklaracją innej funkcji, nadpisanie tej funkcji w wersji globalnej
6 - nadpisywanie zmiennych globalnych w funkcjach
7 - przekazywanie parametrów przez wartość/zmienną
8 - wszystkie dostępne operacje na listach
9 - funkcja zwracająca listę
10 - funkcja przyjmująca referencje na liste oraz wartość listy jako parametry
11 - zagnieżdzona funkcja, przykład statycznego typowania 
12 - jeszcze ptzykład rekurencji
13 - wzajemna rekurencja 2 funkcji (tzn w f wywołujemy g, a w g - f)


W plikach badXX.lb są programy:
1,2,3,5 - błędy parsowania.
6/7 - niezadeklarowana zmienna/funkcja.
8 - zła liczba argumentów funkcji
9 - wywołanie bez przypisania funkcji typu innego niż void
10 - przypisanie wyniku funkcji typu void na zmienną
11 - porównanie zmiennych różnych typów
12 - nie poprawny typ zmiennej przy przypisywaniu
13 - nie poprawny typ parametru funkcji
14 - dzielenie przez 0
15 - odwołanie się do ujemnego indeksu na liście
16 - indeks przekracza długość listy
17 - próba przekazania wyrażenia arytmetycznego jako fartość parametru int&
18 - prosty przykład pokazujący, że faza kontroli typów jest przed wykonaniem programu (czyli tutaj przed sprawdzeniem, że dzielimy nielegalnie przez 0)
