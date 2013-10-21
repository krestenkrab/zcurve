-module(zcurve).

%%
%% Encoding Z-Order Curves.   See http://en.wikipedia.org/wiki/Z-order_curve
%%

%% primary API
-export([ranges/2, ranges/3,
         encode/1, encode/2,
         decode/2, decode/3]).

%% Utility function for debugging, uses ranges/3, then
%% decodes the resulting ranges as symbolic points.
-export([ranges2/2, ranges2/3]).

-define(DEFAULT_BITS, 32).

%% The maximum search space overhead.  A larger number will result in ranges/2
%% returning fewer search segments covering larger areas (up to MAX_SEARCH times
%% the requested search ares).  MAX_SEARCH==1 produce an exact range, which may
%% require many small search ranges.
-define(MAX_SEARCH, 10).

%% use a tuple like a 0-based array
-define(aget(T,I), element(I+1, T)).
-define(aset(T,I, V), setelement(I+1, T, V)).

%% @doc Encode an N-dimensional point to a 32-bit unsigned integer.
%% The domain of each dimension is limited to `32 div size(Tup)' bits.
-spec encode( Tup :: { 0..16#ffff , 0..16#ffff }
                   | { 0..16#3ff, 0..16#3ff, 0..16#3ff }
                   | { 0..16#ff, 0..16#ff, 0..16#ff, 0..16#ff } ) -> 0..16#ffffffff.
encode(Tup) ->
    encode(Tup, ?DEFAULT_BITS).

%% @doc encode an N-dimensional point to a scalar
%% Each dimension value should be an integer 
-spec encode( Tup :: tuple(), TotalBits :: pos_integer() ) -> pos_integer().
encode(Tup, TotalBits) ->
    Dims = size(Tup),
    BitsPerDim = TotalBits div Dims,
    MaxValue = (1 bsl BitsPerDim) - 1,
    List = lists:map(fun(V) when is_integer(V), V >= 0, V =< MaxValue -> V;
                        (V) -> exit({badarg, V}) end,
                     lists:reverse(tuple_to_list(Tup))),
    Bin = zval(<<>>, List, BitsPerDim-1, List),
    BitSize = BitsPerDim * Dims,
    <<N:BitSize>> = Bin,
    N.

zval(Z, _, -1, _) ->
    Z;
zval(Z, [Val|Rest], Step, All) ->
    Bit = (Val bsr Step) band 1,
    zval(<<Z/bitstring, Bit:1>>, Rest, Step, All);
zval(Z, [], Step, All) ->
    zval(Z, All, Step-1, All).

%% decode a scalar value into it's constituent dimensions
-spec decode(Scalar :: pos_integer(), Dims :: pos_integer() ) -> tuple().
decode(Scalar, Dims) ->
    decode(Scalar, Dims, ?DEFAULT_BITS).

%% decode a scalar value into it's constituent dimensions
decode(Scalar, Dims, TotalBits) ->
    BitsPerDim = TotalBits div Dims,
    BitSize = BitsPerDim * Dims,
    Tup = erlang:make_tuple(Dims, 0),
    unz(<<Scalar:BitSize>>, Tup, BitSize-1, Dims).

unz(<<>>, Tup, _, _) ->
    Tup;
unz(<<1:1,Rest/bitstring>>, Tup, BS, Dims) ->
    Dim = BS rem Dims,
    Pos = BS div Dims,
    Added = ?aget(Tup, Dim) bor (1 bsl Pos),
    NewTup = ?aset(Tup, Dim, Added),
    unz(Rest, NewTup, BS-1, Dims);
unz(<<0:1,Rest/bitstring>>, Tup, BS, Dims) ->
    unz(Rest, Tup, BS-1, Dims).



ranges(Min,Max) ->
    ranges(Min, Max, ?DEFAULT_BITS).

ranges(Min,Max, Bits)
  when is_tuple(Min), is_tuple(Max), size(Min)==size(Max) ->
    Len = size(Min),

    {Min2, Max2} = fix_min_max(Min,Max),

    Total = get_size(Min2, Max2, Len),

    List = morton_ranges([], Min2, Max2, Len, 0, Bits),

    io:format("ranges: ~p~n", [length(List)]),

    combine(lists:sort(List), Total, 1 bsl Len).

ranges2(Min,Max) ->
    ranges2(Min, Max, ?DEFAULT_BITS).

ranges2(Min,Max, TotalBits) ->
    Dims = size(Min),
    [ { decode(From, Dims, TotalBits),
        decode(To, Dims, TotalBits) } || {From,To} <- ranges(Min,Max) ].

get_size(Min, Max, Len) ->
    lists:foldl(fun(I,Size) ->
                        Diff = element(I, Max) - element(I, Min),
                        Size * (Diff + 1)
                end,
                1,
                lists:seq(1, Len)).

combine(List, Total, Max) ->
    combine(List, Total, Max, 2).

combine(List, Total, _, MinGap)
  when MinGap >= Total ->
    List;

combine(List, Total, Max, MinGap) ->
    case reduce(List, MinGap) of
        List2 when length(List) =< Max ->
            List2;
        List2 ->
            Searched = lists:sum([High-Low+1 || {Low,High} <- List2]),

            if
                Searched > ?MAX_SEARCH * Total ->
                    List;
                true ->
                    combine(List2, Total, Max, MinGap + (MinGap div 2))
            end
    end.


reduce(List, MinGap) ->
    reduce(List, MinGap, []).

reduce([], _, List) ->
    lists:reverse(List);
reduce([{Low0,High0}, {Low1,High1} | Rest], MinGap, Acc)
  when (Low1-High0) =< MinGap ->
    reduce([{Low0, High1}|Rest], MinGap, Acc);
reduce([Interval|Rest], MinGap, Acc) ->
    reduce(Rest, MinGap, [Interval|Acc]).



morton_ranges(List, Min, Max, Len, Level, Bits)
  when Level =< 10 ->

    %% Find the dimension that has the larges range
    {SplitDim, _, Size} =
        lists:foldl(fun(I, {Largest, LargestDiff, Size}) ->
                            Diff = ?aget(Max,I)-?aget(Min,I),
                            Size2 = Size * (Diff + 1),
                            if Diff > LargestDiff ->
                                    {I, Diff, Size2};
                               true ->
                                    {Largest, LargestDiff, Size2}
                            end
                    end,
                    {0, 0, 1},
                    lists:seq(0, Len-1)),

    Low = encode(Min, Bits),
    High = encode(Max, Bits),
    Range = High - Low - 1,

    if
        Range =< Size ->
            [{Low,High}|List];

        true ->
            Middle = middle(?aget(Min,SplitDim),?aget(Max,SplitDim)),
            List2 = morton_ranges(List, Min, ?aset(Max, SplitDim, Middle), Len, Level+1, Bits),
            morton_ranges(List2, ?aset(Min, SplitDim, Middle+1), Max, Len, Level+1, Bits)
    end;
morton_ranges(List, Min, Max, _Len, _Level, Bits) ->
    Low = encode(Min, Bits),
    High = encode(Max, Bits),
    [{Low,High}|List].

middle(A,B) ->
    case B-A-1 of
        0 -> A;
        1 -> A+1;
        Diff ->
            Scale = compute_power2(Diff),
            case roundUp(A+2, 1 bsl Scale) - 1 of
                M when M > A; M < B -> M
            end
    end.

roundUp(X, Power) ->
    (X + Power - 1) band (-Power).

%% compute MSB bit position
compute_power2(Value) ->
    compute_power2(0, Value).

compute_power2(Power, Value)
  when (1 bsl Power) < Value ->
       compute_power2(Power+1, Value);
compute_power2(Power, _) ->
    Power - 1.

%% make sure Min[idx] < Max[idx] for all idx by swapping coordinates
fix_min_max(Min, Max) ->

    {MinList, MaxList} =
        lists:unzip(
          [ if A > B -> {B,A};
               true  -> {A,B} end
            || {A,B} <- lists:zip( erlang:tuple_to_list(Min),
                                   erlang:tuple_to_list(Max) ) ]),

    { erlang:list_to_tuple(MinList),
      erlang:list_to_tuple(MaxList) }.


