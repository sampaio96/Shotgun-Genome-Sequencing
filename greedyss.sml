structure SS =
struct

    structure Seq = SeqUtils(ArraySequence)

    datatype base = A | C | T | G
        
    type dna = base Seq.seq
        
    (* Assumes length(s) <= length(t)

       Let n = length(s)
       times are independent of length(t) (because take is)

       length : constant time
       take : O(n) work, O(1) span
       equal : O(n) work, O(log n) span

       overall O(n) work, O(log n) span
       *)
    fun isPrefix (s : dna, t : dna) : bool = 
        Seq.equal (op=) (s, Seq.take t (Seq.length s))

    (* Let |s| = length(s), |t| = length(t), n = min(|s|,|t|)
       
       nonEmptySuffixes : O(n^2) work, O(1) span (because length(stail) = n)
       each isPrefix: O(n) work, O(log n) span 
       filter: O(n^2) work, O(log n) span 

       overall: O(n^2) work, O(log n) span
       note that this is also O(|s| |t|) work, O(log |m|) span, 
       because n was the min of these.  
       *)
    fun overlap (s : dna, t : dna) : int = 
        let (* the maximum overlap cannot be longer than the shorter string, 
               so it suffices to restrict to the suffix of s and the prefix of t
               whose lengths are the min of |s| and |t|
               *)
            val maxoverlap = Int.min(Seq.length s, Seq.length t)
            val stail = Seq.tail s maxoverlap
            val thead = Seq.take t maxoverlap
            val prefixes = Seq.filter (fn suff => isPrefix (suff,thead)) (Seq.nonEmptySuffixes stail)
        in 
            case Seq.splitHead prefixes of
                Seq.NIL => 0
              | Seq.CONS(x,_) => Seq.length x
        end

    (* assumes length(s) >= 2 

       Let n = length(snips), 
           m = sum of lengths of all snips

           Note m >= n because no empty snips

       All distinct pairs: O(n^2) work, O(1) span
       Overlaps map (TRICKY): 
          W <= Sum_{all distinct snippets s and t}(W_overlaps(s,t)) 
            <= Sum_{all distinct snippets s and t}(k (|s| |t|)) 
            <= Sum_{all snippets s and t}(k (|s| |t|)) 
            <= Sum_{s}(k |s| * Sum_{t} |t|)
            <= Sum_{s}(k |s| * m)
            <= km Sum_{s}(|s|)
            <= km^2
          So work is O(m^2)

          The span is bounded by log(longest snip) and therefore log(m).  

       Max: O(n^2) work, O(log n) span

       removed filter: O(n) work, O(log n) span

       sum of all: O(m^2 + n^2) work, O(log(mn))
       b/c m>n:    O(m^2) work, O(log m) span

     *)
    fun removeBestOverlap (snips : dna Seq.seq) : dna Seq.seq * (dna * int * dna) =
        let val overlaps = Seq.map (fn ((i,x),(j,y)) => (overlap (x,y), (i,x), (j,y)))
                                   (Seq.allDistinctPairsIdx snips)
            val (overlap,(leftidx,left),(rightidx,right)) = 
                Seq.max (fn ((o1,_,_),(o2,_,_)) => Int.compare (o1,o2)) overlaps
            val removed = Seq.filterIdx (fn (j,_) => j <> leftidx andalso j <> rightidx) snips
        in 
            (removed, (left, overlap, right))
        end

    (* append: O(length(s) + length(t)) work, O(1) span 
       drop: O(length(t)) work, O(1) span

       Overall: O(length(s) + length(t)) work, O(1) span
     *)
    fun join (s : dna, ov : int, t : dna) : dna  = Seq.append (s, Seq.drop t ov)

    (* Example of contraction.  

       Let n = length(snips), 
           m = sum of length of all snips

       T(n,m) <= T(n-1,m) + time for helper functions because
       - removeBestOverlap removes two things, and then we reinsert 1
       - m is no bigger in the recursive call (likely smaller)

       join: O(m) work, O(1) span
       cons: O(n) work, O(1) span
       removeBestOverlap: O(m^2) work, O(log(m)) span

       So 
       W(n,m) <= W(n-1,m) + O(m^2)
       S(n,m) <= S(n-1,m) + O(log(m))

       and W(n,m) is O( n * m^2 ) 
           S(n,m) is O( n * log(m) ) 
     *)
    fun greedy (snips : dna Seq.seq) : dna =
        case Seq.splitMid snips of
            Seq.EMPTY => raise Fail "no data"
          | Seq.ONE x => x
          | _ => let val (rest, best) = removeBestOverlap snips
                      in 
                           greedy (Seq.cons (join best) rest)
                      end

    val example : dna Seq.seq = 
        Seq.fromList [ Seq.fromList [ C,A,T,T ] ,
                       Seq.fromList [ G,A,G,T,A,T ], 
                       Seq.fromList [ T,A,G,G],
                       Seq.fromList [ T,T,A],
                       Seq.fromList [ G,G,A]
                      ]
         
end