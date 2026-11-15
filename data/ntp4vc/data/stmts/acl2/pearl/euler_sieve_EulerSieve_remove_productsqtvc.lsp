;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/euler_sieve_EulerSieve_remove_productsqtvc: the signed 63-bit
;; verification condition for removing products in an Euler sieve.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Signed 63-bit words are represented by their signed integer values.  This
;; interval representation is bijective, so word equality is integer equality.

(defun rp-bv63-p (x)
  (and
   (integerp x)
   (<= (- (expt 2 62)) x)
   (< x (expt 2 62))))

(defun rp-int63-in-bounds-p (x)
  (rp-bv63-p x))

(defun rp-int-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (rp-int-list-p (cdr xs)))))

(defun rp-bool-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (booleanp (car xs))
     (rp-bool-list-p (cdr xs)))))

(defun rp-int-to-nat (x)
  (if (and (integerp x) (< x 0))
      0
    (nfix x)))

;; Source list operations are total: out-of-range integer entries default to
;; zero, Boolean entries default to false, and List.set is a no-op.

(defun rp-nth-int (i xs)
  (let ((value (nth (rp-int-to-nat i) xs)))
    (if (integerp value) value 0)))

(defun rp-nth-bool (i xs)
  (let ((value (nth (rp-int-to-nat i) xs)))
    (if (booleanp value) value nil)))

(defun rp-list-set (xs index value)
  (if (< (rp-int-to-nat index) (len xs))
      (update-nth (rp-int-to-nat index) value xs)
    xs))

;; Machine division truncates toward zero.  Modulo by two in the source is
;; Euclidean and therefore agrees with ACL2 MOD.

(defun rp-tdiv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor (abs numerator) (abs denominator))))
        (if
            (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun rp-emod (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (mod numerator denominator)
    0))

;; A direct full-domain characterization of primality on natural numbers.

(defun-sk rp-prime-divisors-p (n)
  (forall (d)
    (implies
     (and
      (integerp d)
      (<= 1 d)
      (equal (mod n d) 0))
     (or (equal d 1) (equal d n)))))

(defun rp-prime-p (n)
  (and
   (integerp n)
   (<= 2 n)
   (rp-prime-divisors-p n)))

;; The state type and its three accessors remain arbitrary.  Every typing and
;; invariant requirement from the source is explicit in the statement context.

(defstub rp-state-p (x) t)
(defstub rp-nexts (x) t)
(defstub rp-marked (x) t)
(defstub rp-max (x) t)

;; EulerSieveSpec predicates.

(defun-sk rp-inv-nexts-p (nexts n)
  (forall (i)
    (implies
     (and (integerp i) (<= 0 i) (< i n))
     (and
      (< i (rp-nth-int i nexts))
      (<= (rp-nth-int i nexts) n)))))

(defun-sk rp-eliminated-between-p (marked nexts i)
  (forall (j)
    (implies
     (and
      (integerp j)
      (< i j)
      (< j (rp-nth-int i nexts)))
     (equal (rp-nth-bool j marked) t))))

(defun-sk rp-all-eliminated-index-p (marked nexts)
  (forall (i)
    (implies
     (and (integerp i) (<= 0 i) (< i (len marked)))
     (rp-eliminated-between-p marked nexts i))))

(defun rp-all-eliminated-marked-p (marked nexts)
  (and
   (equal (len marked) (len nexts))
   (rp-all-eliminated-index-p marked nexts)))

(defun-sk rp-partial-eliminated-index-p (marked nexts min)
  (forall (i)
    (implies
     (and (integerp i) (<= min i) (< i (len marked)))
     (rp-eliminated-between-p marked nexts i))))

(defun rp-all-eliminated-marked-partial-p
    (marked nexts min)
  (and
   (equal (len marked) (len nexts))
   (rp-partial-eliminated-index-p marked nexts min)))

(defun-sk rp-all-primes-p (marked n)
  (forall (i)
    (implies
     (and (integerp i) (<= 0 i) (< i n))
     (iff
      (not (equal (rp-nth-bool i marked) t))
      (rp-prime-p (rp-int-to-nat i))))))

(defun-sk rp-all-multiples-index-p (marked i max)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= 2 k)
      (< k max)
      (< (* i k) (len marked)))
     (equal (rp-nth-bool (* i k) marked) t))))

(defun rp-all-multiples-marked-p (marked i max)
  (and
   (<= 2 i)
   (< i (len marked))
   (rp-all-multiples-index-p marked i max)))

(defun-sk rp-previously-marked-multiples-p (marked n)
  (forall (i)
    (implies
     (and (integerp i) (<= 2 i) (< i n))
     (rp-all-multiples-marked-p marked i (len marked)))))

(defun-sk rp-only-multiples-witness-p (k n bound)
  (exists (i j)
    (and
     (integerp i)
     (integerp j)
     (<= 2 i)
     (< i n)
     (<= 2 j)
     (< j bound)
     (equal (* i j) k))))

(defun-sk rp-only-multiples-index-p (marked n)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= 2 k)
      (< k (len marked))
      (equal (rp-nth-bool k marked) t))
     (rp-only-multiples-witness-p k n (len marked)))))

(defun rp-only-multiples-marked-p (marked n)
  (rp-only-multiples-index-p marked n))

(defun-sk rp-prime-multiples-index-p
    (marked-old marked n max)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= n i)
      (< i max)
      (not (equal (rp-nth-bool i marked-old) t))
      (< (* n i) (len marked-old)))
     (equal (rp-nth-bool (* n i) marked) t))))

(defun rp-prime-multiples-marked-p
    (marked-old marked n max)
  (and
   (equal (len marked-old) (len marked))
   (< n max)
   (<= max (len marked))
   (rp-prime-multiples-index-p
    marked-old marked n max)))

(defun rp-inv-remove-products-p (nexts marked n)
  (and
   (equal (len nexts) (len marked))
   (not (equal (rp-nth-bool 2 marked) t))
   (rp-all-primes-p marked n)
   (rp-prime-p (rp-int-to-nat n))
   (not (equal (rp-nth-bool n marked) t))
   (rp-inv-nexts-p nexts (len nexts))))

(defun-sk rp-not-marked-next-index-p (marked nexts n)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 2 i)
      (<= i (rp-tdiv (- (len marked) 1) n))
      (<=
       (rp-nth-int i nexts)
       (rp-tdiv (- (len marked) 1) n))
      (not (equal (rp-nth-bool i marked) t)))
     (not
      (equal
       (rp-nth-bool (rp-nth-int i nexts) marked)
       t)))))

(defun rp-not-marked-impl-next-not-marked-p
    (marked nexts n)
  (and
   (equal (len marked) (len nexts))
   (<= 2 (len marked))
   (<= 2 n)
   (rp-not-marked-next-index-p marked nexts n)))

(defun-sk rp-is-copy-index-p (marked marked-old)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len marked))
      (not (equal (rp-nth-bool i marked) t)))
     (not (equal (rp-nth-bool i marked-old) t)))))

(defun rp-is-copy-p (marked marked-old)
  (and
   (equal (len marked) (len marked-old))
   (rp-is-copy-index-p marked marked-old)))

(defun-sk rp-not-marked-next-partial-index-p
    (marked nexts n p)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 2 i)
      (< i p)
      (<=
       (rp-nth-int i nexts)
       (rp-tdiv (- (len marked) 1) n))
      (not (equal (rp-nth-bool i marked) t)))
     (not
      (equal
       (rp-nth-bool (rp-nth-int i nexts) marked)
       t)))))

(defun rp-not-marked-impl-next-not-marked-partial-p
    (marked nexts n p)
  (and
   (equal (len marked) (len nexts))
   (<= 2 (len marked))
   (<= 2 n)
   (<= p (rp-tdiv (- (len marked) 1) n))
   (rp-not-marked-next-partial-index-p
    marked nexts n p)))

;; The universal clauses of t'invariant.

(defun-sk rp-state-even-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (<= i (rp-max self))
      (equal (rp-emod i 2) 0))
     (equal (rp-nth-bool i (rp-marked self)) t))))

(defun-sk rp-state-odd-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (< i (- (rp-max self) 1))
      (equal (rp-emod i 2) 1))
     (or
      (equal
       (rp-emod (rp-nth-int i (rp-nexts self)) 2)
       1)
      (equal
       (rp-nth-int i (rp-nexts self))
       (+ (rp-max self) 1))))))

(defun rp-state-invariant-p (self)
  (and
   (< (rp-max self) (- (expt 2 62) 1))
   (<= 3 (rp-max self))
   (equal (len (rp-nexts self)) (len (rp-marked self)))
   (equal (len (rp-marked self)) (+ (rp-max self) 1))
   (rp-inv-nexts-p (rp-nexts self) (len (rp-nexts self)))
   (rp-all-eliminated-marked-p
    (rp-marked self) (rp-nexts self))
   (rp-state-even-p self)
   (rp-state-odd-p self)
   (equal
    (rp-nth-int (rp-max self) (rp-nexts self))
    (+ (rp-max self) 1))
   (implies
    (equal (rp-emod (- (rp-max self) 1) 2) 0)
    (equal
     (rp-nth-int (- (rp-max self) 1) (rp-nexts self))
     (rp-max self)))
   (implies
    (equal (rp-emod (- (rp-max self) 1) 2) 1)
    (equal
     (rp-nth-int (- (rp-max self) 1) (rp-nexts self))
     (+ (rp-max self) 1)))))

(defun-sk rp-state-nonempty-p ()
  (exists (self)
    (rp-state-p self)))

(defun-sk rp-state-context-p ()
  (forall (self)
    (implies
     (rp-state-p self)
     (and
      (rp-int-list-p (rp-nexts self))
      (rp-bool-list-p (rp-marked self))
      (rp-bv63-p (rp-max self))
      (rp-state-invariant-p self)))))

(defun rp-context-p ()
  (and
   (rp-state-nonempty-p)
   (rp-state-context-p)))

;; The source loop invariant, factored only to expose its repeated identical
;; occurrences in the verification condition.

(defun rp-loop-invariant-p
    (self marked-old n max1 p x)
  (and
   (<= n p)
   (<= p max1)
   (<= 3 n)
   (<= n max1)
   (equal (rp-emod p 2) 1)
   (<= p x)
   (< x (rp-nth-int p (rp-nexts self)))
   (equal
    (rp-nth-int x (rp-nexts self))
    (rp-nth-int p (rp-nexts self)))
   (equal (rp-nth-bool (* n n) (rp-marked self)) t)
   (rp-inv-remove-products-p
    (rp-nexts self) (rp-marked self) n)
   (rp-previously-marked-multiples-p
    (rp-marked self) n)
   (not (equal (rp-nth-bool p (rp-marked self)) t))
   (rp-is-copy-p (rp-marked self) marked-old)
   (rp-all-eliminated-marked-partial-p
    marked-old (rp-nexts self) x)
   (rp-not-marked-impl-next-not-marked-p
    marked-old (rp-nexts self) n)
   (rp-prime-multiples-marked-p
    marked-old
    (rp-marked self)
    n
    (rp-nth-int x (rp-nexts self)))
   (rp-not-marked-impl-next-not-marked-partial-p
    (rp-marked self) (rp-nexts self) n p)
   (rp-only-multiples-marked-p
    (rp-marked self) (+ n 1))))

(defun rp-fallback-p (self marked-old n)
  (and
   (rp-inv-remove-products-p
    (rp-nexts self) (rp-marked self) n)
   (rp-not-marked-impl-next-not-marked-p
    (rp-marked self)
    (rp-nexts self)
    (rp-nth-int n (rp-nexts self)))
   (rp-is-copy-p (rp-marked self) marked-old)
   (rp-previously-marked-multiples-p
    (rp-marked self) n)
   (rp-prime-multiples-marked-p
    marked-old (rp-marked self) n (len (rp-marked self)))
   (rp-only-multiples-marked-p
    (rp-marked self) (+ n 1))))

(defun rp-final-p (self n)
  (let ((next-n (rp-nth-int n (rp-nexts self))))
    (and
     (rp-inv-remove-products-p
      (rp-nexts self) (rp-marked self) n)
     (rp-not-marked-impl-next-not-marked-p
      (rp-marked self) (rp-nexts self) next-n)
     (rp-previously-marked-multiples-p
      (rp-marked self) next-n)
     (rp-only-multiples-marked-p
      (rp-marked self) next-n))))

;; Marked-successor branch.

(defun-sk rp-all-j-p (marked p o4)
  (forall (j)
    (implies
     (and (integerp j) (< p j) (< j o4))
     (equal (rp-nth-bool j marked) t))))

(defun-sk rp-all-t4-p
    (t2 t3 marked-old n max1 p next o4)
  (forall (t4)
    (implies
     (rp-state-p t4)
     (implies
      (and
       (equal (rp-marked t4) (rp-marked t3))
       (equal (rp-max t4) (rp-max t3)))
      (implies
       (equal
        (rp-nexts t4)
        (rp-list-set (rp-nexts t3) p o4))
       (and
        (<=
         0
         (- max1 (rp-nth-int p (rp-nexts t2))))
        (<
         (- max1 (rp-nth-int p (rp-nexts t4)))
         (- max1 (rp-nth-int p (rp-nexts t2))))
        (rp-loop-invariant-p
         t4 marked-old n max1 p next)))))))

(defun-sk rp-all-o4-p
    (t2 t3 marked-old n max1 p next)
  (forall (o4)
    (implies
     (and
      (rp-bv63-p o4)
      (<= 3 o4)
      (<= o4 (+ (rp-max t3) 1))
      (equal o4 (rp-nth-int next (rp-nexts t3)))
      (or
       (equal (rp-emod o4 2) 1)
       (equal o4 (+ (rp-max t3) 1))))
     (and
      (<= 0 p)
      (<= p (rp-max t3))
      (< p o4)
      (<= o4 (+ (rp-max t3) 1))
      (equal (rp-emod p 2) 1)
      (rp-all-j-p (rp-marked t3) p o4)
      (not (equal (rp-nth-bool p (rp-marked t3)) t))
      (or
       (equal (rp-emod o4 2) 1)
       (equal o4 (+ (rp-max t3) 1)))
      (rp-all-t4-p
       t2 t3 marked-old n max1 p next o4)))))

(defun rp-t3-continuation-p
    (t2 t3 marked-old n max1 p next)
  (and
   (<= 0 next)
   (<= next (rp-max t3))
   (equal (rp-emod next 2) 1)
   (if (equal (rp-nth-bool next (rp-marked t3)) t)
       (and
        (<= 3 next)
        (<= next (rp-max t3))
        (equal (rp-emod next 2) 1)
        (rp-all-o4-p
         t2 t3 marked-old n max1 p next))
     (and
      (<=
       0
       (- max1 (rp-nth-int p (rp-nexts t2))))
      (<
       (- max1 (rp-nth-int next (rp-nexts t3)))
       (- max1 (rp-nth-int p (rp-nexts t2))))
      (rp-loop-invariant-p
       t3 marked-old n max1 next next)))))

(defun-sk rp-all-t3-p
    (t2 marked-old n max1 p next product)
  (forall (t3)
    (implies
     (rp-state-p t3)
     (implies
      (and
       (equal (rp-nexts t3) (rp-nexts t2))
       (equal (rp-max t3) (rp-max t2)))
      (implies
       (equal
        (rp-marked t3)
        (rp-list-set (rp-marked t2) product t))
       (rp-t3-continuation-p
        t2 t3 marked-old n max1 p next))))))

(defun-sk rp-all-products-p
    (t2 marked-old n max1 p next)
  (forall (product)
    (implies
     (and
      (rp-bv63-p product)
      (equal product (* n next)))
     (and
      (<= 0 product)
      (<= product (rp-max t2))
      (equal (rp-emod product 2) 1)
      (rp-all-t3-p
       t2 marked-old n max1 p next product)))))

(defun rp-o2-branch-p
    (t2 marked-old n max1 d p next o2)
  (if (equal o2 t)
      (if (<= next d)
          (and
           (rp-int63-in-bounds-p (* n next))
           (rp-all-products-p
            t2 marked-old n max1 p next))
        (rp-fallback-p t2 marked-old n))
    (rp-fallback-p t2 marked-old n)))

(defun-sk rp-all-o2-p
    (t2 marked-old n max1 d p next)
  (forall (o2)
    (implies
     (booleanp o2)
     (implies
      (if (<= 0 next)
          (and
           (<= 2 (rp-max t2))
           (equal
            o2
            (if (<= next (rp-max t2)) t nil)))
        (equal o2 nil))
      (rp-o2-branch-p
       t2 marked-old n max1 d p next o2)))))

(defun-sk rp-all-next-p
    (t2 marked-old n max1 d p)
  (forall (next)
    (implies
     (and
      (rp-bv63-p next)
      (<= 3 next)
      (<= next (+ (rp-max t2) 1))
      (equal next (rp-nth-int p (rp-nexts t2)))
      (or
       (equal (rp-emod next 2) 1)
       (equal next (+ (rp-max t2) 1))))
     (rp-all-o2-p
      t2 marked-old n max1 d p next))))

(defun-sk rp-all-p-x-p
    (t2 marked-old n max1 d)
  (forall (p x)
    (implies
     (and (rp-bv63-p p) (integerp x))
     (implies
      (rp-loop-invariant-p
       t2 marked-old n max1 p x)
      (and
       (<= 3 p)
       (<= p (rp-max t2))
       (equal (rp-emod p 2) 1)
       (rp-all-next-p
        t2 marked-old n max1 d p))))))

(defun-sk rp-all-loop-states-p (t1 n d)
  (forall (t2)
    (implies
     (rp-state-p t2)
     (implies
      (equal (rp-max t2) (rp-max t1))
      (rp-all-p-x-p
       t2 (rp-marked t1) n (rp-max t1) d)))))

;; Initial marking branch for n*n.

(defun-sk rp-all-final-t3-p (t2 marked-old n)
  (forall (t3)
    (implies
     (rp-state-p t3)
     (implies
      (equal (rp-max t3) (rp-max t2))
      (implies
       (rp-fallback-p t3 marked-old n)
       (rp-final-p t3 n))))))

(defun-sk rp-all-square-t2-p (t1 n square)
  (forall (t2)
    (implies
     (rp-state-p t2)
     (implies
      (and
       (equal (rp-nexts t2) (rp-nexts t1))
       (equal (rp-max t2) (rp-max t1)))
      (implies
       (equal
        (rp-marked t2)
        (rp-list-set (rp-marked t1) square t))
       (and
        (rp-loop-invariant-p
         t2 (rp-marked t1) n (rp-max t1) n n)
        (rp-all-final-t3-p
         t2 (rp-marked t1) n)))))))

(defun-sk rp-all-squares-p (t1 n)
  (forall (square)
    (implies
     (and
      (rp-bv63-p square)
      (equal square (* n n)))
     (and
      (<= 0 square)
      (<= square (rp-max t1))
      (equal (rp-emod square 2) 1)
      (rp-all-square-t2-p t1 n square)))))

(defun rp-d-continuation-p (t1 n d)
  (and
   (rp-all-loop-states-p t1 n d)
   (rp-int63-in-bounds-p (* n n))
   (rp-all-squares-p t1 n)))

(defun-sk rp-all-d-p (t1 n)
  (forall (d)
    (implies
     (and
      (rp-bv63-p d)
      (equal d (rp-tdiv (rp-max t1) n)))
     (rp-d-continuation-p t1 n d))))

(defun ntp4vc-pearl-euler-sieve-eulersieve-remove-productsqtvc-statement
    (n t1)
  (implies
   (and
    (rp-context-p)
    (rp-bv63-p n)
    (rp-state-p t1)
    (<= 3 n)
    (<= n (rp-max t1))
    (<= (* n n) (rp-max t1))
    (rp-inv-remove-products-p
     (rp-nexts t1) (rp-marked t1) n)
    (rp-previously-marked-multiples-p
     (rp-marked t1) n)
    (rp-only-multiples-marked-p
     (rp-marked t1) n)
    (rp-not-marked-impl-next-not-marked-p
     (rp-marked t1) (rp-nexts t1) n))
   (implies
    (<= 2 (rp-max t1))
    (and
     (not (equal n 0))
     (rp-int63-in-bounds-p
      (rp-tdiv (rp-max t1) n))
     (rp-all-d-p t1 n)))))

(value-triple :itpeval-statement-checked)
:q
