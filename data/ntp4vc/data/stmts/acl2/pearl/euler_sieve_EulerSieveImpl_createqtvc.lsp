;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/euler_sieve_EulerSieveImpl_createqtvc: the integer and signed
;; 63-bit verification condition for constructing the initial Euler-sieve
;; arrays and their invariants. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Signed 63-bit words are represented by their signed integer values.  This
;; interval representation is bijective, so word equality is integer equality.

(defun ntp4vc-euler-sieve-bv63-p (x)
  (and
   (integerp x)
   (<= (- (expt 2 62)) x)
   (< x (expt 2 62))))

(defun ntp4vc-euler-sieve-int63-in-bounds-p (x)
  (ntp4vc-euler-sieve-bv63-p x))

(defun ntp4vc-euler-sieve-int-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-euler-sieve-int-list-p (cdr xs)))))

(defun ntp4vc-euler-sieve-bool-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (booleanp (car xs))
     (ntp4vc-euler-sieve-bool-list-p (cdr xs)))))

(defun ntp4vc-euler-sieve-int-to-nat (x)
  (if (and (integerp x) (< x 0))
      0
    (nfix x)))

;; The source list lookup is total: integer lists default to zero and Boolean
;; lists default to false.

(defun ntp4vc-euler-sieve-nth-int (i xs)
  (let ((value
         (nth
          (ntp4vc-euler-sieve-int-to-nat i)
          xs)))
    (if (integerp value) value 0)))

(defun ntp4vc-euler-sieve-nth-bool (i xs)
  (let ((value
         (nth
          (ntp4vc-euler-sieve-int-to-nat i)
          xs)))
    (if (booleanp value) value nil)))

;; Truncated division is used by the machine-integer conversions; Euclidean
;; division and modulo are used by the mathematical invariants.

(defun ntp4vc-euler-sieve-tdiv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if
            (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun ntp4vc-euler-sieve-ediv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (floor numerator denominator)
    0))

(defun ntp4vc-euler-sieve-emod (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (mod numerator denominator)
    0))

(defun ntp4vc-euler-sieve-set-list (xs index value)
  (if (< (nfix index) (len xs))
      (update-nth (nfix index) value xs)
    xs))

;; The source array and result types are abstract and nonempty.  Conservative
;; predicates and accessors retain arbitrary interpretations; their complete
;; typing, invariants, and extensionality assumptions are stated below.

(defstub ntp4vc-euler-sieve-array63-p (x) t)
(defstub ntp4vc-euler-sieve-array-elts (x) t)
(defstub ntp4vc-euler-sieve-array-size (x) t)

(defstub ntp4vc-euler-sieve-result-p (x) t)
(defstub ntp4vc-euler-sieve-result-nexts (x) t)
(defstub ntp4vc-euler-sieve-result-marked (x) t)
(defstub ntp4vc-euler-sieve-result-arr (x) t)
(defstub ntp4vc-euler-sieve-result-max (x) t)
(defstub ntp4vc-euler-sieve-result-max-arr (x) t)

(defun-sk ntp4vc-euler-sieve-array-elements-in-bounds-p (a)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len (ntp4vc-euler-sieve-array-elts a))))
     (ntp4vc-euler-sieve-int63-in-bounds-p
      (ntp4vc-euler-sieve-nth-int
       i
       (ntp4vc-euler-sieve-array-elts a))))))

(defun ntp4vc-euler-sieve-array-invariant-p (a)
  (and
   (integerp (ntp4vc-euler-sieve-array-size a))
   (ntp4vc-euler-sieve-int-list-p
    (ntp4vc-euler-sieve-array-elts a))
   (<= 0 (ntp4vc-euler-sieve-array-size a))
   (equal
    (ntp4vc-euler-sieve-array-size a)
    (len (ntp4vc-euler-sieve-array-elts a)))
   (<=
    (len (ntp4vc-euler-sieve-array-elts a))
    (- (expt 2 62) 1))
   (ntp4vc-euler-sieve-array-elements-in-bounds-p a)))

(defun-sk ntp4vc-euler-sieve-array-nonempty-p ()
  (exists (a)
    (ntp4vc-euler-sieve-array63-p a)))

(defun-sk ntp4vc-euler-sieve-array-context-p ()
  (forall (a)
    (implies
     (ntp4vc-euler-sieve-array63-p a)
     (ntp4vc-euler-sieve-array-invariant-p a))))

;; EulerSieveSpec.inv_nexts.

(defun-sk ntp4vc-euler-sieve-inv-nexts-p (nexts n)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i n))
     (and
      (< i (ntp4vc-euler-sieve-nth-int i nexts))
      (<= (ntp4vc-euler-sieve-nth-int i nexts) n)))))

(defun-sk ntp4vc-euler-sieve-eliminated-between-p
    (marked nexts i)
  (forall (j)
    (implies
     (and
      (integerp j)
      (< i j)
      (< j (ntp4vc-euler-sieve-nth-int i nexts)))
     (equal
      (ntp4vc-euler-sieve-nth-bool j marked)
      t))))

(defun-sk ntp4vc-euler-sieve-all-eliminated-index-p
    (marked nexts)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len marked)))
     (ntp4vc-euler-sieve-eliminated-between-p
      marked nexts i))))

(defun ntp4vc-euler-sieve-all-eliminated-marked-p
    (marked nexts)
  (and
   (equal (len marked) (len nexts))
   (ntp4vc-euler-sieve-all-eliminated-index-p
    marked nexts)))

;; The universal indexed clauses of the source result invariant.

(defun-sk ntp4vc-euler-sieve-result-invariant-j-p (self i)
  (forall (j)
    (implies
     (and
      (integerp j)
      (< i j)
      (<
       j
       (ntp4vc-euler-sieve-ediv
        (abs
         (ntp4vc-euler-sieve-nth-int
          i
          (ntp4vc-euler-sieve-array-elts
           (ntp4vc-euler-sieve-result-arr self))))
        2)))
     (<
      (ntp4vc-euler-sieve-nth-int
       j
       (ntp4vc-euler-sieve-array-elts
        (ntp4vc-euler-sieve-result-arr self)))
      0))))

(defun-sk ntp4vc-euler-sieve-result-invariant-even-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (<= i (ntp4vc-euler-sieve-result-max self))
      (equal (ntp4vc-euler-sieve-emod i 2) 0))
     (equal
      (ntp4vc-euler-sieve-nth-bool
       i
       (ntp4vc-euler-sieve-result-marked self))
      t))))

(defun-sk ntp4vc-euler-sieve-result-invariant-odd-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (< i (- (ntp4vc-euler-sieve-result-max self) 1))
      (equal (ntp4vc-euler-sieve-emod i 2) 1))
     (or
      (equal
       (ntp4vc-euler-sieve-emod
        (ntp4vc-euler-sieve-nth-int
         i
         (ntp4vc-euler-sieve-result-nexts self))
        2)
       1)
      (equal
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-result-nexts self))
       (+ (ntp4vc-euler-sieve-result-max self) 1))))))

(defun-sk ntp4vc-euler-sieve-result-invariant-range-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i (ntp4vc-euler-sieve-result-max-arr self)))
     (and
      (<=
       (- (+ (ntp4vc-euler-sieve-result-max self) 1))
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-array-elts
         (ntp4vc-euler-sieve-result-arr self))))
      (<=
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-array-elts
         (ntp4vc-euler-sieve-result-arr self)))
       (+ (ntp4vc-euler-sieve-result-max self) 1))))))

(defun-sk ntp4vc-euler-sieve-result-invariant-sign-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i (ntp4vc-euler-sieve-result-max-arr self)))
     (iff
      (equal
       (ntp4vc-euler-sieve-nth-bool
        (+ (* 2 i) 1)
        (ntp4vc-euler-sieve-result-marked self))
       t)
      (<
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-array-elts
         (ntp4vc-euler-sieve-result-arr self)))
       0)))))

(defun-sk ntp4vc-euler-sieve-result-invariant-unmarked-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i (ntp4vc-euler-sieve-result-max-arr self))
      (not
       (equal
        (ntp4vc-euler-sieve-nth-bool
         (+ (* 2 i) 1)
         (ntp4vc-euler-sieve-result-marked self))
        t)))
     (equal
      (ntp4vc-euler-sieve-nth-int
       i
       (ntp4vc-euler-sieve-array-elts
        (ntp4vc-euler-sieve-result-arr self)))
      (ntp4vc-euler-sieve-nth-int
       (+ (* 2 i) 1)
       (ntp4vc-euler-sieve-result-nexts self))))))

(defun-sk ntp4vc-euler-sieve-result-invariant-marked-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i (ntp4vc-euler-sieve-result-max-arr self))
      (equal
       (ntp4vc-euler-sieve-nth-bool
        (+ (* 2 i) 1)
        (ntp4vc-euler-sieve-result-marked self))
       t))
     (equal
      (ntp4vc-euler-sieve-nth-int
       i
       (ntp4vc-euler-sieve-array-elts
        (ntp4vc-euler-sieve-result-arr self)))
      (-
       (ntp4vc-euler-sieve-nth-int
        (+ (* 2 i) 1)
        (ntp4vc-euler-sieve-result-nexts self)))))))

(defun-sk ntp4vc-euler-sieve-result-invariant-jump-p (self)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i (ntp4vc-euler-sieve-result-max-arr self)))
     (and
      (<
       i
       (ntp4vc-euler-sieve-ediv
        (abs
         (ntp4vc-euler-sieve-nth-int
          i
          (ntp4vc-euler-sieve-array-elts
           (ntp4vc-euler-sieve-result-arr self))))
        2))
      (<=
       (ntp4vc-euler-sieve-ediv
        (abs
         (ntp4vc-euler-sieve-nth-int
          i
          (ntp4vc-euler-sieve-array-elts
           (ntp4vc-euler-sieve-result-arr self))))
        2)
       (+ (ntp4vc-euler-sieve-result-max-arr self) 1))
      (<=
       (abs
        (ntp4vc-euler-sieve-nth-int
         i
         (ntp4vc-euler-sieve-array-elts
          (ntp4vc-euler-sieve-result-arr self))))
       (+ (ntp4vc-euler-sieve-result-max self) 1))
      (ntp4vc-euler-sieve-result-invariant-j-p self i)))))

(defun ntp4vc-euler-sieve-result-invariant-index-p (self)
  (and
   (ntp4vc-euler-sieve-result-invariant-even-p self)
   (ntp4vc-euler-sieve-result-invariant-odd-p self)
   (ntp4vc-euler-sieve-result-invariant-range-p self)
   (ntp4vc-euler-sieve-result-invariant-sign-p self)
   (ntp4vc-euler-sieve-result-invariant-unmarked-p self)
   (ntp4vc-euler-sieve-result-invariant-marked-p self)
   (ntp4vc-euler-sieve-result-invariant-jump-p self)))

(defun ntp4vc-euler-sieve-result-invariant-p (self)
  (and
   (<
    (ntp4vc-euler-sieve-result-max self)
    (- (expt 2 62) 1))
   (<= 3 (ntp4vc-euler-sieve-result-max self))
   (equal
    (len (ntp4vc-euler-sieve-result-nexts self))
    (len (ntp4vc-euler-sieve-result-marked self)))
   (equal
    (len (ntp4vc-euler-sieve-result-marked self))
    (+ (ntp4vc-euler-sieve-result-max self) 1))
   (equal
    (ntp4vc-euler-sieve-ediv
     (- (ntp4vc-euler-sieve-result-max self) 1)
     2)
    (ntp4vc-euler-sieve-result-max-arr self))
   (equal
    (len
     (ntp4vc-euler-sieve-array-elts
      (ntp4vc-euler-sieve-result-arr self)))
    (+ (ntp4vc-euler-sieve-result-max-arr self) 1))
   (ntp4vc-euler-sieve-inv-nexts-p
    (ntp4vc-euler-sieve-result-nexts self)
    (len (ntp4vc-euler-sieve-result-nexts self)))
   (ntp4vc-euler-sieve-all-eliminated-marked-p
    (ntp4vc-euler-sieve-result-marked self)
    (ntp4vc-euler-sieve-result-nexts self))
   (ntp4vc-euler-sieve-result-invariant-index-p self)
   (equal
    (ntp4vc-euler-sieve-nth-int
     (ntp4vc-euler-sieve-result-max self)
     (ntp4vc-euler-sieve-result-nexts self))
    (+ (ntp4vc-euler-sieve-result-max self) 1))
   (implies
    (equal
     (ntp4vc-euler-sieve-emod
      (- (ntp4vc-euler-sieve-result-max self) 1)
      2)
     0)
    (equal
     (ntp4vc-euler-sieve-nth-int
      (- (ntp4vc-euler-sieve-result-max self) 1)
      (ntp4vc-euler-sieve-result-nexts self))
     (ntp4vc-euler-sieve-result-max self)))
   (implies
    (equal
     (ntp4vc-euler-sieve-emod
      (- (ntp4vc-euler-sieve-result-max self) 1)
      2)
     1)
    (equal
     (ntp4vc-euler-sieve-nth-int
      (- (ntp4vc-euler-sieve-result-max self) 1)
      (ntp4vc-euler-sieve-result-nexts self))
     (+ (ntp4vc-euler-sieve-result-max self) 1)))))

(defun-sk ntp4vc-euler-sieve-result-nonempty-p ()
  (exists (self)
    (ntp4vc-euler-sieve-result-p self)))

(defun-sk ntp4vc-euler-sieve-result-context-p ()
  (forall (self)
    (implies
     (ntp4vc-euler-sieve-result-p self)
     (and
      (ntp4vc-euler-sieve-int-list-p
       (ntp4vc-euler-sieve-result-nexts self))
      (ntp4vc-euler-sieve-bool-list-p
       (ntp4vc-euler-sieve-result-marked self))
      (ntp4vc-euler-sieve-array63-p
       (ntp4vc-euler-sieve-result-arr self))
      (ntp4vc-euler-sieve-bv63-p
       (ntp4vc-euler-sieve-result-max self))
      (ntp4vc-euler-sieve-bv63-p
       (ntp4vc-euler-sieve-result-max-arr self))
      (ntp4vc-euler-sieve-result-invariant-p self)))))

(defun-sk ntp4vc-euler-sieve-result-injective-context-p ()
  (forall (a b)
    (implies
     (and
      (ntp4vc-euler-sieve-result-p a)
      (ntp4vc-euler-sieve-result-p b)
      (equal
       (ntp4vc-euler-sieve-result-nexts a)
       (ntp4vc-euler-sieve-result-nexts b))
      (equal
       (ntp4vc-euler-sieve-result-marked a)
       (ntp4vc-euler-sieve-result-marked b))
      (equal
       (ntp4vc-euler-sieve-result-arr a)
       (ntp4vc-euler-sieve-result-arr b))
      (equal
       (ntp4vc-euler-sieve-result-max a)
       (ntp4vc-euler-sieve-result-max b))
      (equal
       (ntp4vc-euler-sieve-result-max-arr a)
       (ntp4vc-euler-sieve-result-max-arr b)))
     (equal a b))))

(defun ntp4vc-euler-sieve-context-p ()
  (and
   (ntp4vc-euler-sieve-array-nonempty-p)
   (ntp4vc-euler-sieve-array-context-p)
   (ntp4vc-euler-sieve-result-nonempty-p)
   (ntp4vc-euler-sieve-result-context-p)
   (ntp4vc-euler-sieve-result-injective-context-p)))

;; Exact definitions of the three source initialization functions.

(defun ntp4vc-euler-sieve-fc (max1 i)
  (if (equal i max1)
      (+ max1 1)
    (if (equal i (- max1 1))
        (if (equal (ntp4vc-euler-sieve-emod i 2) 0)
            max1
          (+ max1 1))
      (if (or
           (< i 3)
           (equal (ntp4vc-euler-sieve-emod i 2) 0))
          (+ i 1)
        (+ i 2)))))

(defun ntp4vc-euler-sieve-o1 (i)
  (if
      (or
       (equal i 0)
       (equal i 1)
       (and
        (< 2 i)
        (equal (ntp4vc-euler-sieve-emod i 2) 0)))
      t
    nil))

(defun ntp4vc-euler-sieve-fc1 (max1 len-arr i)
  (if (equal i (- len-arr 1))
      (+ max1 1)
    (if (equal i 0)
        -2
      (+ (* 2 i) 3))))

(defun ntp4vc-euler-sieve-create-nexts-aux
    (remaining index max1)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (ntp4vc-euler-sieve-fc max1 index)
     (ntp4vc-euler-sieve-create-nexts-aux
      (- remaining 1)
      (+ index 1)
      max1))))

(defun ntp4vc-euler-sieve-create-nexts (len max1)
  (ntp4vc-euler-sieve-create-nexts-aux
   (nfix len) 0 max1))

(defun ntp4vc-euler-sieve-create-marked-aux
    (remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (ntp4vc-euler-sieve-o1 index)
     (ntp4vc-euler-sieve-create-marked-aux
      (- remaining 1)
      (+ index 1)))))

(defun ntp4vc-euler-sieve-create-marked (len)
  (ntp4vc-euler-sieve-create-marked-aux
   (nfix len) 0))

(defun-sk ntp4vc-euler-sieve-nexts-created-p
    (nexts1 len max1)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i len))
     (equal
      (ntp4vc-euler-sieve-nth-int i nexts1)
      (ntp4vc-euler-sieve-fc max1 i)))))

(defun-sk ntp4vc-euler-sieve-marked-created-p
    (marked1 len)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i len))
     (equal
      (ntp4vc-euler-sieve-nth-bool i marked1)
      (ntp4vc-euler-sieve-o1 i)))))

(defun-sk ntp4vc-euler-sieve-nonzero-side-condition-p ()
  (forall (i)
    (implies
     (and
      (integerp i)
      (not (equal i 0))
      (not (equal i 1))
      (< 2 i))
     (not (equal 2 0)))))

;; Initial arrays contain -2 at every source index below len_arr.

(defun-sk ntp4vc-euler-sieve-initial-array-elements-p
    (arr1 len-arr)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i len-arr))
     (equal
      (ntp4vc-euler-sieve-nth-int
       i
       (ntp4vc-euler-sieve-array-elts arr1))
      -2))))

(defun-sk ntp4vc-euler-sieve-prefix-fc1-p
    (arr1 max1 len-arr upper)
  (forall (j)
    (implies
     (and
      (integerp j)
      (<= 0 j)
      (< j upper))
     (equal
      (ntp4vc-euler-sieve-nth-int
       j
       (ntp4vc-euler-sieve-array-elts arr1))
      (ntp4vc-euler-sieve-fc1 max1 len-arr j)))))

;; The post-loop invariant, parameterized by the final array.

(defun-sk ntp4vc-euler-sieve-post-invariant-j-p
    (arrx i)
  (forall (j)
    (implies
     (and
      (integerp j)
      (< i j)
      (<
       j
       (ntp4vc-euler-sieve-ediv
        (abs
         (ntp4vc-euler-sieve-nth-int
          i
          (ntp4vc-euler-sieve-array-elts arrx)))
        2)))
     (<
      (ntp4vc-euler-sieve-nth-int
       j
       (ntp4vc-euler-sieve-array-elts arrx))
      0))))

(defun-sk ntp4vc-euler-sieve-post-invariant-even-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (<= i max1)
      (equal (ntp4vc-euler-sieve-emod i 2) 0))
     (equal
      (ntp4vc-euler-sieve-nth-bool i marked1)
      t))))

(defun-sk ntp4vc-euler-sieve-post-invariant-odd-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 3 i)
      (< i (- max1 1))
      (equal (ntp4vc-euler-sieve-emod i 2) 1))
     (or
      (equal
       (ntp4vc-euler-sieve-emod
        (ntp4vc-euler-sieve-nth-int i nexts1)
        2)
       1)
      (equal
       (ntp4vc-euler-sieve-nth-int i nexts1)
       (+ max1 1))))))

(defun-sk ntp4vc-euler-sieve-post-invariant-range-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i o8))
     (and
      (<=
       (- (+ max1 1))
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-array-elts arrx)))
      (<=
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-array-elts arrx))
       (+ max1 1))))))

(defun-sk ntp4vc-euler-sieve-post-invariant-sign-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i o8))
     (iff
      (equal
       (ntp4vc-euler-sieve-nth-bool
        (+ (* 2 i) 1)
        marked1)
       t)
      (<
       (ntp4vc-euler-sieve-nth-int
        i
        (ntp4vc-euler-sieve-array-elts arrx))
       0)))))

(defun-sk ntp4vc-euler-sieve-post-invariant-unmarked-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i o8)
      (not
       (equal
        (ntp4vc-euler-sieve-nth-bool
         (+ (* 2 i) 1)
         marked1)
        t)))
     (equal
      (ntp4vc-euler-sieve-nth-int
       i
       (ntp4vc-euler-sieve-array-elts arrx))
      (ntp4vc-euler-sieve-nth-int
       (+ (* 2 i) 1)
       nexts1)))))

(defun-sk ntp4vc-euler-sieve-post-invariant-marked-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i o8)
      (equal
       (ntp4vc-euler-sieve-nth-bool
        (+ (* 2 i) 1)
        marked1)
       t))
     (equal
      (ntp4vc-euler-sieve-nth-int
       i
       (ntp4vc-euler-sieve-array-elts arrx))
      (-
       (ntp4vc-euler-sieve-nth-int
        (+ (* 2 i) 1)
        nexts1))))))

(defun-sk ntp4vc-euler-sieve-post-invariant-jump-p
    (arrx nexts1 marked1 max1 o8)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i o8))
     (and
      (<
       i
       (ntp4vc-euler-sieve-ediv
        (abs
         (ntp4vc-euler-sieve-nth-int
          i
          (ntp4vc-euler-sieve-array-elts arrx)))
        2))
      (<=
       (ntp4vc-euler-sieve-ediv
        (abs
         (ntp4vc-euler-sieve-nth-int
          i
          (ntp4vc-euler-sieve-array-elts arrx)))
        2)
       (+ o8 1))
      (<=
       (abs
        (ntp4vc-euler-sieve-nth-int
         i
         (ntp4vc-euler-sieve-array-elts arrx)))
       (+ max1 1))
      (ntp4vc-euler-sieve-post-invariant-j-p
       arrx i)))))

(defun ntp4vc-euler-sieve-post-invariant-index-p
    (arrx nexts1 marked1 max1 o8)
  (and
   (ntp4vc-euler-sieve-post-invariant-even-p
    arrx nexts1 marked1 max1 o8)
   (ntp4vc-euler-sieve-post-invariant-odd-p
    arrx nexts1 marked1 max1 o8)
   (ntp4vc-euler-sieve-post-invariant-range-p
    arrx nexts1 marked1 max1 o8)
   (ntp4vc-euler-sieve-post-invariant-sign-p
    arrx nexts1 marked1 max1 o8)
   (ntp4vc-euler-sieve-post-invariant-unmarked-p
    arrx nexts1 marked1 max1 o8)
   (ntp4vc-euler-sieve-post-invariant-marked-p
    arrx nexts1 marked1 max1 o8)
   (ntp4vc-euler-sieve-post-invariant-jump-p
    arrx nexts1 marked1 max1 o8)))

;; The returned Euler-sieve object must expose the constructed fields and
;; satisfy the stated initialization properties.

(defun-sk ntp4vc-euler-sieve-result-odd-unmarked-p
    (result max1)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 1 i)
      (<=
       i
       (ntp4vc-euler-sieve-ediv (- max1 1) 2)))
     (not
      (equal
       (ntp4vc-euler-sieve-nth-bool
        (+ (* 2 i) 1)
        (ntp4vc-euler-sieve-result-marked result))
       t)))))

(defun-sk ntp4vc-euler-sieve-result-even-marked-p
    (result max1)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 2 i)
      (<=
       i
       (ntp4vc-euler-sieve-ediv (+ max1 1) 2))
      (<= (* 2 i) max1))
     (equal
      (ntp4vc-euler-sieve-nth-bool
       (* 2 i)
       (ntp4vc-euler-sieve-result-marked result))
      t))))

(defun-sk ntp4vc-euler-sieve-result-odd-next-p
    (result max1)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 1 i)
      (<=
       i
       (ntp4vc-euler-sieve-ediv (- max1 1) 2))
      (< (+ (* 2 i) 1) (- max1 1)))
     (equal
      (ntp4vc-euler-sieve-nth-int
       (+ (* 2 i) 1)
       (ntp4vc-euler-sieve-result-nexts result))
      (+ (* 2 i) 3)))))

(defun-sk ntp4vc-euler-sieve-result-even-next-p
    (result max1)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 2 i)
      (<=
       i
       (ntp4vc-euler-sieve-ediv (- max1 1) 2))
      (< (* 2 i) (- max1 1)))
     (equal
      (ntp4vc-euler-sieve-nth-int
       (* 2 i)
       (ntp4vc-euler-sieve-result-nexts result))
      (+ (* 2 i) 1)))))

(defun-sk ntp4vc-euler-sieve-result-only-even-marked-p
    (result max1)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (<= i max1)
      (equal
       (ntp4vc-euler-sieve-nth-bool
        i
        (ntp4vc-euler-sieve-result-marked result))
       t))
     (or
      (< i 2)
      (equal
       (ntp4vc-euler-sieve-emod i 2)
       0)))))

(defun ntp4vc-euler-sieve-result-index-properties-p
    (result max1)
  (and
   (ntp4vc-euler-sieve-result-odd-unmarked-p
    result max1)
   (ntp4vc-euler-sieve-result-even-marked-p
    result max1)
   (ntp4vc-euler-sieve-result-odd-next-p
    result max1)
   (ntp4vc-euler-sieve-result-even-next-p
    result max1)
   (ntp4vc-euler-sieve-result-only-even-marked-p
    result max1)))

(defun ntp4vc-euler-sieve-result-properties-p
    (result max1)
  (and
   (equal
    (ntp4vc-euler-sieve-result-max result)
    max1)
   (equal
    (ntp4vc-euler-sieve-nth-bool
     0
     (ntp4vc-euler-sieve-result-marked result))
    (ntp4vc-euler-sieve-nth-bool
     1
     (ntp4vc-euler-sieve-result-marked result)))
   (equal
    (ntp4vc-euler-sieve-nth-bool
     1
     (ntp4vc-euler-sieve-result-marked result))
    t)
   (not
    (equal
     (ntp4vc-euler-sieve-nth-bool
      2
      (ntp4vc-euler-sieve-result-marked result))
     t))
   (ntp4vc-euler-sieve-result-index-properties-p
    result max1)))

(defun-sk ntp4vc-euler-sieve-all-results-p
    (arrx nexts1 marked1 max1 o8)
  (forall (result)
    (implies
     (and
      (ntp4vc-euler-sieve-result-p result)
      (equal
       (ntp4vc-euler-sieve-result-nexts result)
       nexts1)
      (equal
       (ntp4vc-euler-sieve-result-marked result)
       marked1)
      (equal
       (ntp4vc-euler-sieve-result-arr result)
       arrx)
      (equal
       (ntp4vc-euler-sieve-result-max result)
       max1)
      (equal
       (ntp4vc-euler-sieve-result-max-arr result)
       o8))
     (ntp4vc-euler-sieve-result-properties-p
      result max1))))

(defun ntp4vc-euler-sieve-complete-postcondition-p
    (arrx nexts1 marked1 max1 o8)
  (and
   (and
    (< max1 (- (expt 2 62) 1))
    (<= 3 max1))
   (and
    (equal (len nexts1) (len marked1))
    (equal (len marked1) (+ max1 1)))
   (equal
    (ntp4vc-euler-sieve-ediv (- max1 1) 2)
    o8)
   (equal
    (len (ntp4vc-euler-sieve-array-elts arrx))
    (+ o8 1))
   (ntp4vc-euler-sieve-inv-nexts-p
    nexts1 (len nexts1))
   (ntp4vc-euler-sieve-all-eliminated-marked-p
    marked1 nexts1)
   (ntp4vc-euler-sieve-post-invariant-index-p
    arrx nexts1 marked1 max1 o8)
   (equal
    (ntp4vc-euler-sieve-nth-int max1 nexts1)
    (+ max1 1))
   (implies
    (equal
     (ntp4vc-euler-sieve-emod (- max1 1) 2)
     0)
    (equal
     (ntp4vc-euler-sieve-nth-int (- max1 1) nexts1)
     max1))
   (implies
    (equal
     (ntp4vc-euler-sieve-emod (- max1 1) 2)
     1)
    (equal
     (ntp4vc-euler-sieve-nth-int (- max1 1) nexts1)
     (+ max1 1)))
   (ntp4vc-euler-sieve-all-results-p
    arrx nexts1 marked1 max1 o8)))

(defun-sk ntp4vc-euler-sieve-post-o8-p
    (arrx nexts1 marked1 max1 o7)
  (forall (o8)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o8)
      (equal
       o8
       (ntp4vc-euler-sieve-tdiv o7 2)))
     (ntp4vc-euler-sieve-complete-postcondition-p
      arrx nexts1 marked1 max1 o8))))

(defun-sk ntp4vc-euler-sieve-post-o7-p
    (arrx nexts1 marked1 max1)
  (forall (o7)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o7)
      (equal o7 (- max1 1)))
     (and
      (not (equal 2 0))
      (ntp4vc-euler-sieve-int63-in-bounds-p
       (ntp4vc-euler-sieve-tdiv o7 2))
      (ntp4vc-euler-sieve-post-o8-p
       arrx nexts1 marked1 max1 o7)))))

(defun ntp4vc-euler-sieve-post-loop-p
    (arrx nexts1 marked1 max1)
  (and
   (ntp4vc-euler-sieve-int63-in-bounds-p
    (- max1 1))
   (ntp4vc-euler-sieve-post-o7-p
    arrx nexts1 marked1 max1)))

;; One array-update loop iteration.

(defun-sk ntp4vc-euler-sieve-update-witness-condition-p
    (i o7 o8)
  (exists (o9)
    (and
     (ntp4vc-euler-sieve-bv63-p o9)
     (equal o9 (* 2 i))
     (equal o8 (+ o9 3)))))

(defun ntp4vc-euler-sieve-loop-o8-condition-p
    (i o7 o8 max1)
  (if (equal i o7)
      (equal o8 (+ max1 1))
    (ntp4vc-euler-sieve-update-witness-condition-p
     i o7 o8)))

(defun-sk ntp4vc-euler-sieve-updated-prefix-p
    (arr3 max1 len-arr i1)
  (forall (j)
    (implies
     (and
      (integerp j)
      (<= 0 j)
      (< j (+ i1 1)))
     (equal
      (ntp4vc-euler-sieve-nth-int
       j
       (ntp4vc-euler-sieve-array-elts arr3))
      (ntp4vc-euler-sieve-fc1
       max1 len-arr j)))))

(defun-sk ntp4vc-euler-sieve-all-updated-arrays-p
    (arr2 max1 len-arr i o8)
  (forall (arr3)
    (implies
     (and
      (ntp4vc-euler-sieve-array63-p arr3)
      (equal
       (ntp4vc-euler-sieve-array-size arr3)
       (ntp4vc-euler-sieve-array-size arr2))
      (equal
       (ntp4vc-euler-sieve-array-elts arr3)
       (ntp4vc-euler-sieve-set-list
        (ntp4vc-euler-sieve-array-elts arr2)
        i
        o8)))
     (ntp4vc-euler-sieve-updated-prefix-p
      arr3 max1 len-arr i))))

(defun-sk ntp4vc-euler-sieve-loop-o8-p
    (arr2 max1 len-arr i o7)
  (forall (o8)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o8)
      (ntp4vc-euler-sieve-loop-o8-condition-p
       i o7 o8 max1))
     (and
      (<= 0 i)
      (<
       i
       (len
        (ntp4vc-euler-sieve-array-elts arr2)))
      (ntp4vc-euler-sieve-all-updated-arrays-p
       arr2 max1 len-arr i o8)))))

(defun-sk ntp4vc-euler-sieve-loop-double-o8-bounds-p (i)
  (forall (o8)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o8)
      (equal o8 (* 2 i)))
     (ntp4vc-euler-sieve-int63-in-bounds-p
      (+ o8 3)))))

(defun-sk ntp4vc-euler-sieve-loop-o7-p
    (arr2 max1 len-arr i)
  (forall (o7)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o7)
      (equal o7 (- len-arr 1)))
     (implies
      (implies (equal i o7) (equal i o7))
      (and
       (if (equal i o7)
           (ntp4vc-euler-sieve-int63-in-bounds-p
            (+ max1 1))
         (and
          (ntp4vc-euler-sieve-int63-in-bounds-p
           (* 2 i))
          (ntp4vc-euler-sieve-loop-double-o8-bounds-p
           i)))
       (ntp4vc-euler-sieve-loop-o8-p
        arr2 max1 len-arr i o7))))))

(defun-sk ntp4vc-euler-sieve-loop-all-i-p
    (arr2 max1 len-arr o6)
  (forall (i)
    (implies
     (ntp4vc-euler-sieve-bv63-p i)
     (implies
      (and
       (<= 1 i)
       (<= i o6)
       (ntp4vc-euler-sieve-prefix-fc1-p
        arr2 max1 len-arr i))
      (and
       (ntp4vc-euler-sieve-int63-in-bounds-p
        (- len-arr 1))
       (ntp4vc-euler-sieve-loop-o7-p
        arr2 max1 len-arr i))))))

(defun-sk ntp4vc-euler-sieve-all-arr2-p
    (arr1 nexts1 marked1 max1 len-arr o6)
  (forall (arr2)
    (implies
     (and
      (ntp4vc-euler-sieve-array63-p arr2)
      (equal
       (ntp4vc-euler-sieve-array-size arr2)
       (ntp4vc-euler-sieve-array-size arr1)))
     (and
      (ntp4vc-euler-sieve-loop-all-i-p
       arr2 max1 len-arr o6)
      (implies
       (ntp4vc-euler-sieve-prefix-fc1-p
        arr2 max1 len-arr (+ o6 1))
       (ntp4vc-euler-sieve-post-loop-p
        arr2 nexts1 marked1 max1))))))

(defun-sk ntp4vc-euler-sieve-all-o6-p
    (arr1 nexts1 marked1 max1 len-arr)
  (forall (o6)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o6)
      (equal o6 (- len-arr 1)))
     (and
      (implies
       (<= 1 (+ o6 1))
       (and
        (ntp4vc-euler-sieve-prefix-fc1-p
         arr1 max1 len-arr 1)
        (ntp4vc-euler-sieve-all-arr2-p
         arr1 nexts1 marked1 max1 len-arr o6)))
      (implies
       (< (+ o6 1) 1)
       (ntp4vc-euler-sieve-post-loop-p
        arr1 nexts1 marked1 max1))))))

(defun-sk ntp4vc-euler-sieve-all-arr1-p
    (nexts1 marked1 max1 len-arr)
  (forall (arr1)
    (implies
     (and
      (ntp4vc-euler-sieve-array63-p arr1)
      (ntp4vc-euler-sieve-initial-array-elements-p
       arr1 len-arr)
      (equal
       (len (ntp4vc-euler-sieve-array-elts arr1))
       len-arr))
     (and
      (ntp4vc-euler-sieve-int63-in-bounds-p
       (- len-arr 1))
      (ntp4vc-euler-sieve-all-o6-p
       arr1 nexts1 marked1 max1 len-arr)))))

(defun ntp4vc-euler-sieve-lists-and-arrays-p
    (max1 len-arr)
  (let*
      ((len (+ max1 1))
       (nexts1
        (ntp4vc-euler-sieve-create-nexts
         len max1))
       (marked1
        (ntp4vc-euler-sieve-create-marked len)))
    (and
     (<= 0 len)
     (implies
      (and
       (equal (len nexts1) len)
       (ntp4vc-euler-sieve-nexts-created-p
        nexts1 len max1))
      (and
       (ntp4vc-euler-sieve-nonzero-side-condition-p)
       (<= 0 len)
       (implies
        (and
         (equal (len marked1) len)
         (ntp4vc-euler-sieve-marked-created-p
          marked1 len))
        (and
         (<= 0 len-arr)
         (ntp4vc-euler-sieve-all-arr1-p
          nexts1 marked1 max1 len-arr))))))))

(defun-sk ntp4vc-euler-sieve-all-len-arr-p (max1 o3)
  (forall (len-arr)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p len-arr)
      (equal len-arr (+ o3 1)))
     (ntp4vc-euler-sieve-lists-and-arrays-p
      max1 len-arr))))

(defun-sk ntp4vc-euler-sieve-all-o3-p (max1 o2)
  (forall (o3)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o3)
      (equal
       o3
       (ntp4vc-euler-sieve-tdiv o2 2)))
     (and
      (ntp4vc-euler-sieve-int63-in-bounds-p
       (+ o3 1))
      (ntp4vc-euler-sieve-all-len-arr-p
       max1 o3)))))

(defun-sk ntp4vc-euler-sieve-all-o2-p (max1)
  (forall (o2)
    (implies
     (and
      (ntp4vc-euler-sieve-bv63-p o2)
      (equal o2 (- max1 1)))
     (and
      (not (equal 2 0))
      (ntp4vc-euler-sieve-int63-in-bounds-p
       (ntp4vc-euler-sieve-tdiv o2 2))
      (ntp4vc-euler-sieve-all-o3-p
       max1 o2)))))

(defun ntp4vc-pearl-euler-sieve-eulersieveimpl-createqtvc-statement
    (max1)
  (implies
   (and
    (ntp4vc-euler-sieve-context-p)
    (ntp4vc-euler-sieve-bv63-p max1)
    (< max1 (- (expt 2 62) 1))
    (<= 3 max1))
   (and
    (ntp4vc-euler-sieve-int63-in-bounds-p
     (- max1 1))
    (ntp4vc-euler-sieve-all-o2-p max1))))

(value-triple :itpeval-statement-checked)
:q
