;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/longest_increasing_subsequence_Backtracking_lissqtvc: the
;; backtracking longest-increasing-subsequence verification condition over an
;; arbitrary strict total order. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent the arbitrary inhabited source element
;; type and its strict order.  Their typing and order laws are explicit in the
;; final statement predicate.

(defstub lis-elt-p (x) t)
(defstub lis-default-elt () t)
(defstub lis-lt (x y) t)

(defun lis-elt-list-p (xs)
  (if (consp xs)
      (and
       (lis-elt-p (car xs))
       (lis-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun lis-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (lis-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero.  The two accessors implement the
;; source getElem! defaults: zero for integers and the chosen inhabitant for
;; elements.

(defun lis-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

(defun lis-nth-int (index xs)
  (let ((natural-index (lis-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

(defun lis-nth-elt (index xs)
  (let ((natural-index (lis-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (lis-default-elt))))

(defun-sk lis-order-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (lis-elt-p x)
      (lis-elt-p y)
      (lis-elt-p z)
      (lis-lt x y)
      (lis-lt y z))
     (lis-lt x z))))

(defun-sk lis-order-asymmetric-p ()
  (forall (x y)
    (implies
     (and
      (lis-elt-p x)
      (lis-elt-p y)
      (lis-lt x y))
     (not (lis-lt y x)))))

(defun-sk lis-order-trichotomy-p ()
  (forall (x y)
    (implies
     (and
      (lis-elt-p x)
      (lis-elt-p y))
     (or
      (lis-lt x y)
      (lis-lt y x)
      (equal x y)))))

(defun lis-background-p ()
  (and
   (lis-elt-p (lis-default-elt))
   (lis-order-transitive-p)
   (lis-order-asymmetric-p)
   (lis-order-trichotomy-p)))

;; ISS is the source definition of a strictly increasing subsequence encoded
;; by an integer list of indices.

(defun-sk lis-iss-indices-in-bounds-p (s w)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (len s)))
      (and
       (<= 0 (lis-nth-int i s))
       (< (lis-nth-int i s)
          (len w)))))))

(defun-sk lis-iss-increasing-p (s w)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i j)
       (< j (len s)))
      (and
       (< (lis-nth-int i s)
          (lis-nth-int j s))
       (lis-lt
        (lis-nth-elt (lis-nth-int i s) w)
        (lis-nth-elt (lis-nth-int j s) w)))))))

(defun lis-iss-p (s w)
  (and
   (lis-integer-list-p s)
   (lis-elt-list-p w)
   (lis-iss-indices-in-bounds-p s w)
   (lis-iss-increasing-p s w)))

(defun-sk lis-no-longer-iss-p (s w)
  (forall (other)
    (implies
     (lis-integer-list-p other)
     (implies
      (lis-iss-p other w)
      (<= (len other)
          (len s))))))

(defun lis-liss-p (s w)
  (and
   (lis-iss-p s w)
   (lis-no-longer-iss-p s w)))

;; Repeated optimality predicates from the verification condition.

(defun-sk lis-best-two-step-p (s w first upper)
  (forall (other)
    (implies
     (lis-integer-list-p other)
     (implies
      (and
       (lis-iss-p other w)
       (<= 2 (len other))
       (equal (lis-nth-int 0 other) first)
       (< first (lis-nth-int 1 other))
       (< (lis-nth-int 1 other) upper))
      (<= (len other)
          (len s))))))

(defun-sk lis-best-starting-at-p (s w first)
  (forall (other)
    (implies
     (lis-integer-list-p other)
     (implies
      (and
       (lis-iss-p other w)
       (<= 1 (len other))
       (equal (lis-nth-int 0 other) first))
      (<= (len other)
          (len s))))))

(defun-sk lis-best-first-below-p (s w upper)
  (forall (other)
    (implies
     (lis-integer-list-p other)
     (implies
      (and
       (lis-iss-p other w)
       (<= 1 (len other))
       (< (lis-nth-int 0 other) upper))
      (<= (len other)
          (len s))))))

(defun lis-inner-state-p (s state-length w first upper)
  (and
   (equal state-length (len s))
   (< 0 (len s))
   (equal (lis-nth-int 0 s) first)
   (lis-iss-p s w)
   (lis-best-two-step-p s w first upper)))

(defun lis-start-final-state-p (s state-length w first)
  (and
   (equal state-length (len s))
   (< 0 (len s))
   (equal (lis-nth-int 0 s) first)
   (lis-iss-p s w)
   (lis-best-starting-at-p s w first)))

;; The construction facts for CONS are retained as the antecedent appearing
;; in the source VC, rather than simplified away.

(defun-sk lis-cons-tail-equalities-p (combined tail)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< 0 index)
       (<= index (len tail)))
      (equal
       (lis-nth-int index combined)
       (lis-nth-int (- index 1) tail))))))

(defun lis-extension-result-p
    (s state-length w first current successor)
  (if (< state-length
         (+ 1 (len successor)))
      (let ((combined (cons first successor)))
        (implies
         (and
          (equal (len combined)
                 (+ 1 (len successor)))
          (equal (lis-nth-int 0 combined)
                 first)
          (lis-cons-tail-equalities-p
           combined successor))
         (lis-inner-state-p
          combined
          (+ 1 (len successor))
          w first (+ current 1))))
    (lis-inner-state-p
     s state-length w first (+ current 1))))

(defun-sk lis-all-successors-p
    (s state-length w first current)
  (forall (successor)
    (implies
     (lis-integer-list-p successor)
     (implies
      (and
       (< 0 (len successor))
       (equal (lis-nth-int 0 successor)
              current)
       (lis-iss-p successor w)
       (lis-best-starting-at-p
        successor w current))
      (lis-extension-result-p
       s state-length w first current successor)))))

(defun lis-inner-iteration-p
    (s state-length w first current)
  (if (lis-lt
       (lis-nth-elt first w)
       (lis-nth-elt current w))
      (and
       (and
        (<= 0 (- (len w) first))
        (< (- (len w) current)
           (- (len w) first)))
       (<= 0 current)
       (< current (len w))
       (lis-all-successors-p
        s state-length w first current))
    (lis-inner-state-p
     s state-length w first (+ current 1))))

(defun-sk lis-inner-iterations-p
    (s state-length w first lower upper)
  (forall (current)
    (implies
     (integerp current)
     (implies
      (and
       (<= lower current)
       (<= current upper)
       (lis-inner-state-p
        s state-length w first current))
      (lis-inner-iteration-p
       s state-length w first current)))))

(defun lis-inner-loop-result-p
    (s state-length w first lower upper)
  (and
   (lis-inner-iterations-p
    s state-length w first lower upper)
   (implies
    (lis-inner-state-p
     s state-length w first (+ upper 1))
    (lis-start-final-state-p
     s state-length w first))))

(defun-sk lis-all-inner-states-p (w first lower upper)
  (forall (s state-length)
    (implies
     (and
      (lis-integer-list-p s)
      (integerp state-length))
     (lis-inner-loop-result-p
      s state-length w first lower upper))))

(defun lis-index-backtracking-result-p (w first)
  (let* ((singleton (list first))
         (upper (- (len w) 1))
         (lower (+ first 1)))
    (and
     (implies
      (<= lower (+ upper 1))
      (and
       (lis-inner-state-p
        singleton 1 w first lower)
       (lis-all-inner-states-p
        w first lower upper)))
     (implies
      (< (+ upper 1) lower)
      (lis-start-final-state-p
       singleton 1 w first)))))

(defun-sk lis-all-starting-indices-p (w)
  (forall (first)
    (implies
     (integerp first)
     (implies
      (and
       (<= 0 first)
       (< first (len w)))
      (let ((singleton (list first)))
        (implies
         (and
          (equal (len singleton) 1)
          (equal (lis-nth-int 0 singleton)
                 first))
         (lis-index-backtracking-result-p
          w first)))))))

;; The outer loop combines the optimal subsequence for each starting index.

(defun lis-outer-state-p (s state-length w upper)
  (and
   (equal state-length (len s))
   (lis-iss-p s w)
   (lis-best-first-below-p s w upper)))

(defun lis-outer-choice-result-p
    (s state-length w current choice)
  (if (< state-length (len choice))
      (and
       (lis-iss-p choice w)
       (lis-best-first-below-p
        choice w (+ current 1)))
    (and
     (equal state-length (len s))
     (lis-iss-p s w)
     (lis-best-first-below-p
      s w (+ current 1)))))

(defun-sk lis-all-outer-choices-p
    (s state-length w current)
  (forall (choice)
    (implies
     (lis-integer-list-p choice)
     (implies
      (and
       (< 0 (len choice))
       (equal (lis-nth-int 0 choice)
              current)
       (lis-iss-p choice w)
       (lis-best-starting-at-p
        choice w current))
      (lis-outer-choice-result-p
       s state-length w current choice)))))

(defun lis-outer-iteration-p
    (s state-length w current)
  (and
   (<= 0 current)
   (< current (len w))
   (lis-all-outer-choices-p
    s state-length w current)))

(defun-sk lis-outer-iterations-p
    (s state-length w upper)
  (forall (current)
    (implies
     (integerp current)
     (implies
      (and
       (<= 0 current)
       (<= current upper)
       (lis-outer-state-p
        s state-length w current))
      (lis-outer-iteration-p
       s state-length w current)))))

(defun lis-outer-loop-result-p
    (s state-length w upper)
  (and
   (lis-outer-iterations-p
    s state-length w upper)
   (implies
    (lis-outer-state-p
     s state-length w (+ upper 1))
    (and
     (equal state-length (len s))
     (lis-liss-p s w)))))

(defun-sk lis-all-outer-states-p (w upper)
  (forall (s state-length)
    (implies
     (and
      (lis-integer-list-p s)
      (integerp state-length))
     (lis-outer-loop-result-p
      s state-length w upper))))

(defun lis-whole-backtracking-result-p (w)
  (let ((upper (- (len w) 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (equal 0 (len nil))
       (lis-iss-p nil w)
       (lis-best-first-below-p nil w 0)
       (lis-all-outer-states-p w upper)))
     (implies
      (< (+ upper 1) 0)
      (and
       (equal 0 (len nil))
       (lis-liss-p nil w))))))

(defun
  ntp4vc-pearl-longest-increasing-subsequence-backtracking-lissqtvc-statement
  (w)
  (implies
   (and
    (lis-background-p)
    (lis-elt-list-p w))
   (and
    (lis-all-starting-indices-p w)
    (lis-whole-backtracking-result-p w))))

(value-triple :itpeval-statement-checked)
:q
