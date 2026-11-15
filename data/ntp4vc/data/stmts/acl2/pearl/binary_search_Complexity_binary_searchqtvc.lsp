;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binary_search_Complexity_binary_searchqtvc: the binary-search
;; verification condition with its logarithmic time-bound invariant.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integer
;; values and lists.  Int.toNat maps negative integers to zero, and List.get!
;; on an integer list returns the integer default zero outside the list.

(defun ntp4vc-bsearch-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-bsearch-integer-list-p (cdr xs)))))

(defun ntp4vc-bsearch-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-bsearch-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-bsearch-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; Int.tdiv and Isabelle cdiv truncate the integer quotient toward zero.

(defun ntp4vc-bsearch-tdiv (numerator denominator)
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

;; The source fixes an arbitrary integer-valued log2 operation satisfying the
;; displayed recursive specification.  The interface is conservative, and
;; its complete typing and defining law are explicit in the statement.

(defstub ntp4vc-bsearch-log2 (n) t)

(defun-sk ntp4vc-bsearch-log2-spec-p ()
  (forall (n)
    (implies
     (integerp n)
     (and
      (integerp
       (ntp4vc-bsearch-log2 n))
      (equal
       (ntp4vc-bsearch-log2 n)
       (if (<= n 1)
           0
         (+
          1
          (ntp4vc-bsearch-log2
           (ntp4vc-bsearch-tdiv n 2)))))))))

(defun ntp4vc-bsearch-f (n)
  (if (equal n 0)
      0
    (+ 1 (ntp4vc-bsearch-log2 n))))

;; The sortedness hypothesis and the exclusion invariants retain their
;; universal quantification over mathematical integer indices.

(defun-sk ntp4vc-bsearch-sorted-p (a)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2)
      (<= 0 i1)
      (<= i1 i2)
      (< i2 (len a)))
     (<=
      (ntp4vc-bsearch-nth-int i1 a)
      (ntp4vc-bsearch-nth-int i2 a)))))

(defun-sk ntp4vc-bsearch-absent-outside-p
    (a v lower upper)
  (forall (i)
    (implies
     (and
      (integerp i)
      (or
       (and
        (<= 0 i)
        (< i lower))
       (and
        (<= upper i)
        (< i (len a)))))
     (not
      (equal
       (ntp4vc-bsearch-nth-int i a)
       v)))))

(defun-sk ntp4vc-bsearch-absent-everywhere-p (a v)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len a)))
     (not
      (equal
       (ntp4vc-bsearch-nth-int i a)
       v)))))

;; This is the complete result required from one loop iteration at state
;; (lo, hi, time), including the two recursive branches and both exit cases.

(defun ntp4vc-bsearch-loop-step-p
    (a v hi lo time)
  (if (< lo hi)
      (and
       (not (equal 2 0))
       (let ((mid
              (+
               lo
               (ntp4vc-bsearch-tdiv
                (- hi lo)
                2))))
         (and
          (<= 0 mid)
          (< mid (len a))
          (if
              (<
               (ntp4vc-bsearch-nth-int mid a)
               v)
              (and
               (<= 0 (- hi lo))
               (<
                (- hi (+ mid 1))
                (- hi lo))
               (<= 0 (+ mid 1))
               (<= (+ mid 1) hi)
               (<= hi (len a))
               (ntp4vc-bsearch-absent-outside-p
                a v (+ mid 1) hi)
               (<=
                (+
                 (- (+ time 1) 0)
                 (ntp4vc-bsearch-f
                  (- hi (+ mid 1))))
                (ntp4vc-bsearch-f (len a))))
            (and
             (<= 0 mid)
             (< mid (len a))
             (if
                 (<
                  v
                  (ntp4vc-bsearch-nth-int mid a))
                 (and
                  (<= 0 (- hi lo))
                  (<
                   (- mid lo)
                   (- hi lo))
                  (<= 0 lo)
                  (<= lo mid)
                  (<= mid (len a))
                  (ntp4vc-bsearch-absent-outside-p
                   a v lo mid)
                  (<=
                   (+
                    (- (+ time 1) 0)
                    (ntp4vc-bsearch-f
                     (- mid lo)))
                   (ntp4vc-bsearch-f (len a))))
               (and
                (or
                 (and
                  (<= 0 mid)
                  (< mid (len a))
                  (equal
                   (ntp4vc-bsearch-nth-int mid a)
                   v))
                 (and
                  (equal mid -1)
                  (ntp4vc-bsearch-absent-everywhere-p
                   a v)))
                (<=
                 (- time 0)
                 (ntp4vc-bsearch-f (len a))))))))))
    (and
     (or
      (and
       (<= 0 -1)
       (< -1 (len a))
       (equal
        (ntp4vc-bsearch-nth-int -1 a)
        v))
      (ntp4vc-bsearch-absent-everywhere-p a v))
     (<=
      (- time 0)
      (ntp4vc-bsearch-f (len a))))))

(defun-sk ntp4vc-bsearch-loop-vc-p (a v)
  (forall (hi lo time)
    (implies
     (and
      (integerp hi)
      (integerp lo)
      (integerp time)
      (<= 0 lo)
      (<= lo hi)
      (<= hi (len a))
      (ntp4vc-bsearch-absent-outside-p
       a v lo hi)
      (<=
       (+
        (- time 0)
        (ntp4vc-bsearch-f
         (- hi lo)))
       (ntp4vc-bsearch-f (len a))))
     (ntp4vc-bsearch-loop-step-p
      a v hi lo time))))

(defun ntp4vc-pearl-binary-search-complexity-binary-searchqtvc-statement
    (a v)
  (implies
   (and
    (ntp4vc-bsearch-integer-list-p a)
    (integerp v)
    (ntp4vc-bsearch-log2-spec-p)
    (ntp4vc-bsearch-sorted-p a))
   (let ((o1 (len a)))
     (and
      (and
       (and
        (<= 0 0)
        (<= 0 o1)
        (<= o1 (len a)))
       (ntp4vc-bsearch-absent-outside-p
        a v 0 o1)
       (<=
        (+
         (- 0 0)
         (ntp4vc-bsearch-f
          (- o1 0)))
        (ntp4vc-bsearch-f (len a))))
      (ntp4vc-bsearch-loop-vc-p a v)))))

(value-triple :itpeval-statement-checked)
:q
