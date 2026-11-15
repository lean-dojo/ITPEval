;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/queens_NQueensSets_t3qtvc: the N-queens finite-set recursive-loop
;; verification condition, including partial solutions, sorted solution maps,
;; finite-set updates, and loop-invariant preservation. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Finite sets of integers are proper duplicate-free lists.  Equality is
;; extensional, so list order is irrelevant and LEN is exactly cardinality.

(defun nq3-int-set-p (set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (and
       (integerp (car set))
       (not (member-equal (car set) (cdr set)))
       (nq3-int-set-p (cdr set)))
    (equal set nil)))

(defun nq3-member-p (x set)
  (if (member-equal x set) t nil))

(defun nq3-subset-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (nq3-member-p (car left) right)
       (nq3-subset-p (cdr left) right))
    t))

(defun nq3-set-equal-p (left right)
  (and
   (nq3-subset-p left right)
   (nq3-subset-p right left)))

(defun nq3-difference (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (if (nq3-member-p (car left) right)
          (nq3-difference (cdr left) right)
        (cons (car left)
              (nq3-difference (cdr left) right)))
    nil))

(defun nq3-insert (x set)
  (if (nq3-member-p x set)
      set
    (cons x set)))

(defun nq3-remove (x set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (if (equal x (car set))
          (nq3-remove x (cdr set))
        (cons (car set)
              (nq3-remove x (cdr set))))
    nil))

(defun nq3-minimum (set)
  (declare (xargs :measure (acl2-count set)))
  (if (consp set)
      (if (consp (cdr set))
          (let ((tail-min (nq3-minimum (cdr set))))
            (if (< (car set) tail-min)
                (car set)
              tail-min))
        (car set))
    0))

;; These conservative evaluators represent arbitrary maps int -> int and
;; int -> int -> int.  Source typing is imposed explicitly below.  The unary
;; update constructor implements Why3/Lean point update exactly.

(defstub nq3-raw-uval (function index) t)
(defstub nq3-bval (function row column) t)

(defun nq3-u-update (function key value)
  (list :nq3-u-update function key value))

(defun nq3-uval (function index)
  (declare (xargs :measure (acl2-count function)))
  (if (and
       (true-listp function)
       (equal (len function) 4)
       (equal (car function) :nq3-u-update))
      (if (equal index (caddr function))
          (cadddr function)
        (nq3-uval (cadr function) index))
    (nq3-raw-uval function index)))

(defun nq3-b-update-val
    (function key replacement-row row column)
  (if (equal row key)
      (nq3-uval replacement-row column)
    (nq3-bval function row column)))

(defun-sk nq3-u-map-p (function)
  (forall (index)
    (implies
     (integerp index)
     (integerp (nq3-uval function index)))))

(defun-sk nq3-b-map-p (function)
  (forall (row column)
    (implies
     (and (integerp row)
          (integerp column))
     (integerp (nq3-bval function row column)))))

;; Prefix equality is extensional on the integer domain.  The row variants
;; express equality between unary maps and rows of a binary solution map.

(defun-sk nq3-eq-prefix-u-p (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (equal
       (nq3-uval left index)
       (nq3-uval right index))))))

(defun-sk nq3-eq-prefix-u-row-p
    (left right-sol right-row bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (equal
       (nq3-uval left index)
       (nq3-bval right-sol right-row index))))))

(defun-sk nq3-eq-prefix-rows-p
    (sol left-row right-row bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (equal
       (nq3-bval sol left-row index)
       (nq3-bval sol right-row index))))))

(defun-sk nq3-row-equal-p
    (left-sol left-row right-sol right-row)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (nq3-bval left-sol left-row index)
      (nq3-bval right-sol right-row index)))))

(defun-sk nq3-sol-prefix-p (left right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (nq3-row-equal-p left index right index)))))

(defun-sk nq3-row-equal-updated-p
    (left left-row base key replacement-row right-row)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (nq3-bval left left-row index)
      (nq3-b-update-val
       base key replacement-row right-row index)))))

(defun-sk nq3-sol-prefix-updated-p
    (left base key replacement-row bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (nq3-row-equal-updated-p
       left index base key replacement-row index)))))

;; Partial N-queens solutions and lexicographic sorting.

(defun-sk nq3-no-conflicts-u-p (function i)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and (<= 0 j)
           (< j i))
      (and
       (not (equal
             (nq3-uval function i)
             (nq3-uval function j)))
       (not (equal
             (- (nq3-uval function i)
                (nq3-uval function j))
             (- i j)))
       (not (equal
             (- (nq3-uval function i)
                (nq3-uval function j))
             (- j i))))))))

(defun-sk nq3-partial-u-p (n k function)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and (<= 0 i)
           (< i k))
      (and
       (<= 0 (nq3-uval function i))
       (< (nq3-uval function i) n)
       (nq3-no-conflicts-u-p function i))))))

(defun-sk nq3-lt-sol-p (sol left-row right-row n)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index n)
     (nq3-eq-prefix-rows-p
      sol left-row right-row index)
     (< (nq3-bval sol left-row index)
        (nq3-bval sol right-row index)))))

(defun-sk nq3-sorted-p (sol lower upper n)
  (forall (left-row right-row)
    (implies
     (and
      (integerp left-row)
      (integerp right-row))
     (implies
      (and
       (<= lower left-row)
       (< left-row right-row)
       (< right-row upper))
      (nq3-lt-sol-p sol left-row right-row n)))))

(defun-sk nq3-eq-prefix-updated-rows-p
    (base key replacement-row left-row right-row bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (equal
       (nq3-b-update-val
        base key replacement-row left-row index)
       (nq3-b-update-val
        base key replacement-row right-row index))))))

(defun-sk nq3-lt-sol-updated-p
    (base key replacement-row left-row right-row n)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index n)
     (nq3-eq-prefix-updated-rows-p
      base key replacement-row left-row right-row index)
     (< (nq3-b-update-val
         base key replacement-row left-row index)
        (nq3-b-update-val
         base key replacement-row right-row index)))))

(defun-sk nq3-sorted-updated-p
    (base key replacement-row lower upper n)
  (forall (left-row right-row)
    (implies
     (and
      (integerp left-row)
      (integerp right-row))
     (implies
      (and
       (<= lower left-row)
       (< left-row right-row)
       (< right-row upper))
      (nq3-lt-sol-updated-p
       base key replacement-row left-row right-row n)))))

;; Quantified clauses used by the loop invariant and postcondition.

(defun-sk nq3-order-cut-p (initial remaining)
  (forall (i j)
    (implies
     (and (integerp i)
          (integerp j))
     (implies
      (and
       (nq3-member-p
        i
        (nq3-difference initial remaining))
       (nq3-member-p j remaining))
      (< i j)))))

;; Rows of a binary solution map use the same partial-solution definition.

(defun-sk nq3-no-conflicts-row-p (sol row i)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and (<= 0 j)
           (< j i))
      (and
       (not (equal
             (nq3-bval sol row i)
             (nq3-bval sol row j)))
       (not (equal
             (- (nq3-bval sol row i)
                (nq3-bval sol row j))
             (- i j)))
       (not (equal
             (- (nq3-bval sol row i)
                (nq3-bval sol row j))
             (- j i))))))))

(defun-sk nq3-partial-row-p (n k sol row)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and (<= 0 i)
           (< i k))
      (and
       (<= 0 (nq3-bval sol row i))
       (< (nq3-bval sol row i) n)
       (nq3-no-conflicts-row-p sol row i))))))

(defun-sk nq3-recorded-rows-exact-p
    (n k col sol lower upper initial remaining)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (and
       (nq3-partial-row-p n n sol index)
       (nq3-eq-prefix-u-row-p col sol index k)
       (nq3-member-p
        (nq3-bval sol index k)
        (nq3-difference initial remaining)))))))

(defun-sk nq3-row-match-exists-p
    (function sol lower upper n)
  (exists (index)
    (and
     (integerp index)
     (<= lower index)
     (< index upper)
     (nq3-eq-prefix-u-row-p
      function sol index n))))

(defun-sk nq3-loop-completeness-p
    (n k col sol lower upper initial remaining)
  (forall (function)
    (implies
     (nq3-u-map-p function)
     (implies
      (and
       (nq3-partial-u-p n n function)
       (nq3-eq-prefix-u-p col function k)
       (nq3-member-p
        (nq3-uval function k)
        (nq3-difference initial remaining)))
      (and
       (nq3-member-p
        (nq3-uval function k)
        initial)
       (not
        (nq3-member-p
         (nq3-uval function k)
         remaining))
       (nq3-row-match-exists-p
        function sol lower upper n))))))

(defun nq3-loop-invariant-p
    (n k old-col old-sol lower initial remaining
       upper current-col current-sol a b c)
  (and
   (<= 0 (- upper lower))
   (nq3-subset-p
    remaining
    (nq3-difference
     (nq3-difference a b)
     c))
   (nq3-partial-u-p n k current-col)
   (nq3-sorted-p current-sol lower upper n)
   (nq3-order-cut-p initial remaining)
   (nq3-recorded-rows-exact-p
    n k current-col current-sol
    lower upper initial remaining)
   (nq3-loop-completeness-p
    n k current-col current-sol
    lower upper initial remaining)
   (nq3-eq-prefix-u-p old-col current-col k)
   (nq3-sol-prefix-p old-sol current-sol lower)))

(defun-sk nq3-post-all-functions-p
    (n k col sol lower upper)
  (forall (function)
    (implies
     (nq3-u-map-p function)
     (iff
      (and
       (nq3-partial-u-p n n function)
       (nq3-eq-prefix-u-p col function k))
      (nq3-row-match-exists-p
       function sol lower upper n)))))

(defun nq3-postcondition-p
    (n k old-col old-sol lower upper new-col new-sol)
  (and
   (<= 0 (- upper lower))
   (nq3-sorted-p new-sol lower upper n)
   (nq3-post-all-functions-p
    n k new-col new-sol lower upper)
   (nq3-eq-prefix-u-p old-col new-col k)
   (nq3-sol-prefix-p old-sol new-sol lower)))

;; Source precondition characterizations of A, B, and C.

(defun-sk nq3-a-column-free-p (k col i)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and (<= 0 j)
           (< j k))
      (not (equal (nq3-uval col j) i))))))

(defun-sk nq3-a-characterization-p (n k col a)
  (forall (i)
    (implies
     (integerp i)
     (iff
      (nq3-member-p i a)
      (and
       (<= 0 i)
       (< i n)
       (nq3-a-column-free-p k col i))))))

(defun-sk nq3-b-diagonal-free-p (k col i)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and (<= 0 j)
           (< j k))
      (not
       (equal
        (nq3-uval col j)
        (- (+ i j) k)))))))

(defun-sk nq3-b-characterization-p (k col b)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (<= 0 i)
      (iff
       (not (nq3-member-p i b))
       (nq3-b-diagonal-free-p k col i))))))

(defun-sk nq3-c-diagonal-free-p (k col i)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and (<= 0 j)
           (< j k))
      (not
       (equal
        (nq3-uval col j)
        (- (+ i k) j)))))))

(defun-sk nq3-c-characterization-p (k col c)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (<= 0 i)
      (iff
       (not (nq3-member-p i c))
       (nq3-c-diagonal-free-p k col i))))))

;; Finite-set characterizations generated by SUCC and PRED.

(defun-sk nq3-o4-characterization-p (o4 o3)
  (forall (i)
    (implies
     (integerp i)
     (iff
      (nq3-member-p i o4)
      (and
       (<= 0 i)
       (nq3-member-p (+ i 1) o3))))))

(defun-sk nq3-o6-characterization-p (o6 o5)
  (forall (i)
    (implies
     (integerp i)
     (iff
      (nq3-member-p i o6)
      (and
       (<= 1 i)
       (nq3-member-p (- i 1) o5))))))

;; The recursive call's postcondition and the following loop-invariant update.

(defun nq3-o8-result-p
    (n k a b c s col sol o2 e s1
       s2 sol2 col2 o8)
  (and
   (and
    (<= 0 (len e))
    (< (len o8) (len e)))
   (equal
    (+ (- s1 s)
       (- s2 s1))
    (- s2 s))
   (equal (- (+ k 1) 1) k)
   (nq3-loop-invariant-p
    n
    (- (+ k 1) 1)
    col sol s o2 o8 s2 col2 sol2 a b c)))

(defun-sk nq3-all-o8-p
    (n k a b c s col sol o2 e s1 d
       s2 sol2 col2)
  (forall (o8)
    (implies
     (nq3-int-set-p o8)
     (implies
      (and
       (nq3-set-equal-p
        o8
        (nq3-remove d e))
       (if (nq3-member-p d e)
           (equal (len o8)
                  (- (len e) 1))
         (equal (len o8)
                (len e))))
      (nq3-o8-result-p
       n k a b c s col sol o2 e s1
       s2 sol2 col2 o8)))))

(defun-sk nq3-all-recursive-posts-p
    (n k a b c s col sol o2 e s1 sol1 col1 d)
  (forall (s2 sol2 col2)
    (implies
     (and
      (integerp s2)
      (nq3-b-map-p sol2)
      (nq3-u-map-p col2))
     (implies
      (nq3-postcondition-p
       n
       (+ k 1)
       (nq3-u-update col1 k d)
       sol1
       s1 s2 col2 sol2)
      (nq3-all-o8-p
       n k a b c s col sol o2 e s1 d
       s2 sol2 col2)))))

(defun nq3-o7-result-p
    (n k a b c s col sol o2 e s1 sol1 col1
       d o4 o6 o7)
  (and
   (and
    (<= 0 (len a))
    (< (len o7) (len a)))
   (<= 0 (+ k 1))
   (equal
    (+ (+ k 1) (len o7))
    n)
   (<= 0 s1)
   (nq3-a-characterization-p
    n (+ k 1)
    (nq3-u-update col1 k d)
    o7)
   (nq3-b-characterization-p
    (+ k 1)
    (nq3-u-update col1 k d)
    o6)
   (nq3-c-characterization-p
    (+ k 1)
    (nq3-u-update col1 k d)
    o4)
   (nq3-partial-u-p
    n (+ k 1)
    (nq3-u-update col1 k d))
   (nq3-all-recursive-posts-p
    n k a b c s col sol o2 e s1 sol1 col1 d)))

(defun-sk nq3-all-o7-p
    (n k a b c s col sol o2 e s1 sol1 col1
       d o4 o6)
  (forall (o7)
    (implies
     (nq3-int-set-p o7)
     (implies
      (and
       (nq3-set-equal-p
        o7
        (nq3-remove d a))
       (if (nq3-member-p d a)
           (equal (len o7)
                  (- (len a) 1))
         (equal (len o7)
                (len a))))
      (nq3-o7-result-p
       n k a b c s col sol o2 e s1 sol1 col1
       d o4 o6 o7)))))

(defun-sk nq3-all-o6-p
    (n k a b c s col sol o2 e s1 sol1 col1
       d o4 o5)
  (forall (o6)
    (implies
     (nq3-int-set-p o6)
     (implies
      (nq3-o6-characterization-p o6 o5)
      (nq3-all-o7-p
       n k a b c s col sol o2 e s1 sol1 col1
       d o4 o6)))))

(defun-sk nq3-all-o5-p
    (n k a b c s col sol o2 e s1 sol1 col1
       d o4)
  (forall (o5)
    (implies
     (nq3-int-set-p o5)
     (implies
      (and
       (nq3-set-equal-p
        o5
        (nq3-insert d b))
       (if (nq3-member-p d b)
           (equal (len o5)
                  (len b))
         (equal (len o5)
                (+ (len b) 1))))
      (nq3-all-o6-p
       n k a b c s col sol o2 e s1 sol1 col1
       d o4 o5)))))

(defun-sk nq3-all-o4-p
    (n k a b c s col sol o2 e s1 sol1 col1
       d o3)
  (forall (o4)
    (implies
     (nq3-int-set-p o4)
     (implies
      (nq3-o4-characterization-p o4 o3)
      (nq3-all-o5-p
       n k a b c s col sol o2 e s1 sol1 col1
       d o4)))))

(defun-sk nq3-all-o3-p
    (n k a b c s col sol o2 e s1 sol1 col1 d)
  (forall (o3)
    (implies
     (nq3-int-set-p o3)
     (implies
      (and
       (nq3-set-equal-p
        o3
        (nq3-insert d c))
       (if (nq3-member-p d c)
           (equal (len o3)
                  (len c))
         (equal (len o3)
                (+ (len c) 1))))
      (nq3-all-o4-p
       n k a b c s col sol o2 e s1 sol1 col1
       d o3)))))

(defun nq3-loop-result-p
    (n k a b c s col sol o2 e s1 sol1 col1)
  (if (not (equal e nil))
      (and
       (not (equal e nil))
       (nq3-all-o3-p
        n k a b c s col sol o2 e s1 sol1 col1
        (nq3-minimum e)))
    (nq3-postcondition-p
     n k col sol s s1 col1 sol1)))

(defun-sk nq3-all-loop-states-p
    (n k a b c s col sol o2)
  (forall (e s1 sol1 col1)
    (implies
     (and
      (nq3-int-set-p e)
      (integerp s1)
      (nq3-b-map-p sol1)
      (nq3-u-map-p col1))
     (implies
      (nq3-loop-invariant-p
       n k col sol s o2 e s1 col1 sol1 a b c)
      (nq3-loop-result-p
       n k a b c s col sol o2 e s1 sol1 col1)))))

;; Base branch: SOL is updated at S with the current column map.

(defun-sk nq3-eq-prefix-u-updated-row-p
    (left base key replacement-row row bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and (<= 0 index)
           (< index bound))
      (equal
       (nq3-uval left index)
       (nq3-b-update-val
        base key replacement-row row index))))))

(defun-sk nq3-row-match-updated-exists-p
    (function base key replacement-row lower upper n)
  (exists (index)
    (and
     (integerp index)
     (<= lower index)
     (< index upper)
     (nq3-eq-prefix-u-updated-row-p
      function base key replacement-row index n))))

(defun-sk nq3-base-all-functions-p
    (n k col sol s)
  (forall (function)
    (implies
     (nq3-u-map-p function)
     (iff
      (and
       (nq3-partial-u-p n n function)
       (nq3-eq-prefix-u-p col function k))
      (nq3-row-match-updated-exists-p
       function sol s col s (+ s 1) n)))))

(defun nq3-base-result-p (n k s col sol)
  (and
   (equal 1 (- (+ s 1) s))
   (<= 0 (- (+ s 1) s))
   (nq3-sorted-updated-p
    sol s col s (+ s 1) n)
   (nq3-base-all-functions-p
    n k col sol s)
   (nq3-eq-prefix-u-p col col k)
   (nq3-sol-prefix-updated-p
    sol sol s col s)))

;; Quantification over O1 and O2 preserves the exported VC literally.

(defun nq3-o2-result-p
    (n k a b c s col sol o2)
  (and
   (equal 0 (- s s))
   (nq3-loop-invariant-p
    n k col sol s o2 o2 s col sol a b c)
   (nq3-all-loop-states-p
    n k a b c s col sol o2)))

(defun-sk nq3-all-o2-p
    (n k a b c s col sol o1)
  (forall (o2)
    (implies
     (nq3-int-set-p o2)
     (implies
      (nq3-set-equal-p
       o2
       (nq3-difference o1 c))
      (nq3-o2-result-p
       n k a b c s col sol o2)))))

(defun-sk nq3-all-o1-p
    (n k a b c s col sol)
  (forall (o1)
    (implies
     (nq3-int-set-p o1)
     (implies
      (nq3-set-equal-p
       o1
       (nq3-difference a b))
      (nq3-all-o2-p
       n k a b c s col sol o1)))))

(defun nq3-conclusion-p
    (n k a b c s col sol)
  (if (not (equal a nil))
      (nq3-all-o1-p
       n k a b c s col sol)
    (nq3-base-result-p
     n k s col sol)))

(defun-sk
  ntp4vc-pearl-queens-nqueenssets-t3qtvc-statement
  ()
  (forall (n k a s col b c sol)
    (implies
     (and
      (integerp n)
      (integerp k)
      (nq3-int-set-p a)
      (integerp s)
      (nq3-u-map-p col)
      (nq3-int-set-p b)
      (nq3-int-set-p c)
      (nq3-b-map-p sol))
     (implies
      (and
       (<= 0 k)
       (equal (+ k (len a)) n)
       (<= 0 s)
       (nq3-a-characterization-p n k col a)
       (nq3-b-characterization-p k col b)
       (nq3-c-characterization-p k col c)
       (nq3-partial-u-p n k col))
      (nq3-conclusion-p
       n k a b c s col sol)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
