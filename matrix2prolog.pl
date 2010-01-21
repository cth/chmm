/***************************************************************************************
* Reads a matrix file (such as a PAM or blosum matrix) and converts it to Prolog facts.
***************************************************************************************/

readfile(Filename,Chars) :-
	open(Filename,read,Stream),
	read_file_chars(Stream,Chars),
	close(Stream).

read_file_chars(Stream,[Char|Rest]) :-
	get_char(Stream,Char),
	Char \= end_of_file,
	!,
	read_file_chars(Stream,Rest).

read_file_chars(_,[]).

matrix2facts(MatrixFile,FactList) :-
	read_file(MatrixFile,CharList),
	matrix(CharList,[],FactList).


%% DCG for parsing the matrix data
matrix(MatrixFacts) -->
	matrix_header_line(Alphabet),
	matrix_entry_lines(Alphabet,EntryLines),
	{
	 matrix_lines_to_facts(Alphabet,EntryLines)
	}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Header line:

matrix_header_line(SymbolList) -->
	spacer,
	matrix_header_entries(SymbolList),
	maybe_space,
	end_of_line.

matrix_header_entries([]) --> [].

matrix_header_entries([Symbol|Rest]) -->
	matrix_header_entry(Symbol),
	matrix_header_entries(Rest).

matrix_header_entry(Symbol) --> space,	symbol(Symbol).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Entry lines

matrix_entry_lines([],[]) --> [].
		   
matrix_entry_lines([LineSymbol|RestSyms],[LineEntries|LinesRest]) -->
	matrix_entry_line(LineSymbol,LineEntries),
	matrix_entry_lines(RestSyms,LinesRest).

matrix_entry_line(LineSymbol,Entries) -->
	symbol(LineSymbol),
	matrix_entries(Entries),
	maybe_space,
	end_of_line.

matrix_entries([]) --> [].

matrix_entries([Entry|EntriesRest]) -->
	space,
	matrix_entry(Entry),
	matrix_entries(EntriesRest).

matrix_entry(Entry) -->
	numeric(Entry).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Spaces, end_of_line, etc.



% We assume matrix row/column symbols are only one character
symbol(Symbol) --> [ Symbol ].


end_of_line --> {atom_codes('\n',[C])},[C].

maybe_space --> [].
maybe_space --> space.

space --> space1.
space --> space1, space.
space1 --> {atom_codes(' ',[C])}, [C].
space1 --> {atom_codes('\r',[C])}, [C].
space1 --> {atom_codes('\t',[C])}, [C].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Numbers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

numeric(N) --> integer(N).
numeric(N) --> float(N).

integer(I) --> signed_integer(I).
integer(I) --> unsiged_integer(I).

unsigned_integer([D]) -->
	digit(D).
unsigned_integer([D|R]) -->
	digit(D),
	unsiged_integer(R).

signed_integer([S|N]) --> sign(S), unsiged_integer(N).

float(N) -->
	integer(N1),
	['.'],
	integer(N2),
	{append(N1,'.',N3), append(N3,N2,N)}.

sign('-') --> ['-'].
sign('+') --> ['+'].

digit(0) --> ['0'].
digit(1) --> ['1'].
digit(2) --> ['2'].
digit(3) --> ['3'].
digit(4) --> ['4'].
digit(5) --> ['5'].
digit(6) --> ['6'].
digit(7) --> ['7'].
digit(8) --> ['8'].
digit(9) --> ['9'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% TEST

test1 :-
	L = "   A  R  N",
	matrix_header_entries(S,L,[]),
	length(S,3).

test2 :-
	L = "   A  R  N  D  C  Q  E  G  H  I  L  K  M  F  P  S  T  W  Y  V  B  Z  X  *",
	matrix_header_entries(S,L,[]).

test3 :-
	L = "   A  R  N \r\n",
	matrix_header_line(Symbols,L,[]),
	length(Symbols,X),
	write(Symbols),nl,
	write(X),nl.
	
test4 :-
	L = "A  2 -2  0  0",
	matrix_entry_line(65,Entries,L,[]),
	length(Entries,4).
	