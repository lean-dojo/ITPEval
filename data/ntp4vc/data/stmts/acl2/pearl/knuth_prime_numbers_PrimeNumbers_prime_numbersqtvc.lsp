;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc: the verification
;; condition, under the imported Bertrand postulate, for constructing an
;; initial segment of the prime numbers by testing successive odd candidates
;; and recording the next prime.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source uses mathematical integers and integer lists.  Its list
;; projection is total: negative and out-of-range indices return the integer
;; default zero, while nonnegative in-range indices select the corresponding
;; list entry.

(defun knp-integer-list-p (values)
  (if (consp values)
      (and (integerp (car values))
           (knp-integer-list-p (cdr values)))
    (equal values nil)))

(defun knp-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun knp-nth (values index)
  (if (and (integerp index)
           (<= 0 index)
           (< index (len values)))
      (nth index values)
    0))

;; This is exactly List.set: an in-range natural position is replaced, while
;; an out-of-range position leaves the list unchanged.

(defun knp-list-set-nat (values position value)
  (if (consp values)
      (if (zp position)
          (cons value (cdr values))
        (cons (car values)
              (knp-list-set-nat
               (cdr values)
               (- position 1)
               value)))
    nil))

(defun knp-list-set (values index value)
  (knp-list-set-nat values (knp-int-to-nat index) value))

;; Equality between the total list projection after a set and the source
;; Function.update is retained extensionally over every mathematical integer.

(defun-sk knp-update-law-p
    (new-values old-values index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (knp-nth new-values argument)
      (if (equal argument index)
          value
        (knp-nth old-values argument))))))

;; Integer divisibility is used by the trial-division loop.  Natural
;; divisibility is used only to define Nat.Prime (Int.toNat p).

(defun-sk knp-integer-divides-p (divisor value)
  (exists (quotient)
    (and
     (integerp quotient)
     (equal value (* divisor quotient)))))

(defun-sk knp-natural-divides-p (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

(defun-sk knp-no-proper-natural-divisor-p (value)
  (forall (divisor)
    (implies
     (and
      (natp divisor)
      (knp-natural-divides-p divisor value))
     (or
      (equal divisor 1)
      (equal divisor value)))))

(defun knp-prime-p (value)
  (and
   (integerp value)
   (<= 2 value)
   (knp-no-proper-natural-divisor-p value)))

(defun knp-odd-p (value)
  (and
   (integerp value)
   (equal (mod value 2) 1)))

;; no_prime_in l u says that there is no prime strictly between l and u.

(defun-sk knp-no-prime-in-p (lower upper)
  (forall (value)
    (implies
     (and
      (integerp value)
      (< lower value)
      (< value upper))
     (not (knp-prime-p value)))))

;; The source theory imports Bertrand's postulate as an axiom.  It is encoded
;; conservatively here as a predicate and required explicitly by the root
;; statement, rather than admitted as an ACL2 axiom.

(defun-sk knp-bertrand-postulate-p ()
  (forall (value)
    (implies
     (integerp value)
     (implies
      (knp-prime-p value)
      (not
       (knp-no-prime-in-p
        value
        (* 2 value)))))))

;; The four components of first_primes are split only definitionally.

(defun-sk knp-strictly-increasing-before-p (values upper)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j upper))
     (< (knp-nth values i)
        (knp-nth values j)))))

(defun-sk knp-all-prime-before-p (values upper)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i upper))
     (knp-prime-p
      (knp-nth values i)))))

(defun-sk knp-no-prime-gaps-before-p (values upper)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (- upper 1)))
     (knp-no-prime-in-p
      (knp-nth values i)
      (knp-nth values (+ i 1))))))

(defun knp-first-primes-p (values upper)
  (and
   (equal (knp-nth values 0) 2)
   (knp-strictly-increasing-before-p values upper)
   (knp-all-prime-before-p values upper)
   (knp-no-prime-gaps-before-p values upper)))

;; Candidate-search state at index upper: the prefix contains the first
;; primes, and candidate lies strictly between the last recorded prime and
;; twice that prime, is odd, and has no intervening prime.

(defun knp-search-state-p (values upper candidate)
  (let ((last-prime
         (knp-nth values (- upper 1))))
    (and
     (knp-first-primes-p values upper)
     (< last-prime candidate)
     (< candidate (* 2 last-prime))
     (knp-odd-p candidate)
     (knp-no-prime-in-p last-prime candidate))))

(defun-sk knp-no-earlier-divisor-p
    (values candidate bound)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i bound))
     (not
      (knp-integer-divides-p
       (knp-nth values i)
       candidate)))))

(defun knp-trial-state-p
    (values upper candidate divisor-index)
  (and
   (<= 1 divisor-index)
   (< divisor-index upper)
   (knp-search-state-p values upper candidate)
   (knp-no-earlier-divisor-p
    values candidate divisor-index)))

;; This is the conclusion of the innermost trial-division transition.  ACL2's
;; rem and truncate are the source integer tmod and tdiv operations.

(defun knp-inner-transition-conclusion-p
    (values upper candidate divisor-index)
  (let* ((last-prime
          (knp-nth values (- upper 1)))
         (divisor
          (knp-nth values divisor-index))
         (distance
          (- (* 2 last-prime) candidate))
         (next-distance
          (- (* 2 last-prime) (+ candidate 2))))
    (and
     (<= 0 divisor-index)
     (< divisor-index (len values))
     (not (equal divisor 0))
     (if (equal (rem candidate divisor) 0)
         (and
          (or
           (and
            (<= 0 distance)
            (< next-distance distance))
           (and
            (equal distance next-distance)
            (<= 0 (- upper divisor-index))
            (< (- upper 1)
               (- upper divisor-index))))
          (knp-trial-state-p
           values upper (+ candidate 2) 1))
       (and
        (<= 0 divisor-index)
        (< divisor-index (len values))
        (<= 0 divisor-index)
        (< divisor-index (len values))
        (not (equal divisor 0))
        (if (< (knp-nth values divisor-index)
               (truncate candidate divisor))
            (let ((next-index (+ divisor-index 1)))
              (and
               (or
                (and
                 (<= 0 distance)
                 (< distance distance))
                (and
                 (<= 0 (- upper divisor-index))
                 (< (- upper next-index)
                    (- upper divisor-index))))
               (knp-trial-state-p
                values upper candidate next-index)))
          (and
           (< last-prime candidate)
           (knp-prime-p candidate)
           (knp-no-prime-in-p
            last-prime candidate))))))))

(defun-sk knp-inner-transitions-for-candidate-p
    (values upper candidate)
  (forall (divisor-index)
    (implies
     (and
      (integerp divisor-index)
      (knp-trial-state-p
       values upper candidate divisor-index))
     (knp-inner-transition-conclusion-p
      values upper candidate divisor-index))))

(defun-sk knp-all-inner-transitions-p
    (reference-values upper)
  (forall (candidate values)
    (implies
     (and
      (integerp candidate)
      (knp-integer-list-p values)
      (equal (len values)
             (len reference-values)))
     (knp-inner-transitions-for-candidate-p
      values upper candidate))))

;; Once the next prime is found, the source writes it at position upper and
;; re-establishes the prefix and next-candidate state.

(defun-sk knp-record-next-prime-p (values upper)
  (forall (next-prime)
    (implies
     (and
      (integerp next-prime)
      (< (knp-nth values (- upper 1))
         next-prime)
      (knp-prime-p next-prime)
      (knp-no-prime-in-p
       (knp-nth values (- upper 1))
       next-prime))
     (let ((updated
            (knp-list-set values upper next-prime)))
       (and
        (<= 0 upper)
        (< upper (len values))
        (implies
         (equal (len updated)
                (len values))
         (implies
          (knp-update-law-p
           updated values upper next-prime)
          (knp-search-state-p
           updated
           (+ upper 1)
           (+ next-prime 2)))))))))

(defun knp-outer-step-conclusion-p
    (values upper candidate)
  (and
   (knp-all-inner-transitions-p values upper)
   (knp-trial-state-p values upper candidate 1)
   (knp-record-next-prime-p values upper)))

(defun-sk knp-all-outer-steps-p
    (values candidate last-index)
  (forall (upper)
    (implies
     (and
      (integerp upper)
      (<= 2 upper)
      (<= upper last-index)
      (knp-search-state-p
       values upper candidate))
     (knp-outer-step-conclusion-p
      values upper candidate))))

(defun knp-complete-loop-p
    (values candidate last-index requested-length)
  (and
   (knp-all-outer-steps-p
    values candidate last-index)
   (implies
    (knp-search-state-p
     values (+ last-index 1) candidate)
    (and
     (equal (len values) requested-length)
     (knp-first-primes-p
      values requested-length)))))

(defun-sk knp-all-loop-executions-p
    (initial-values last-index requested-length)
  (forall (candidate values)
    (implies
     (and
      (integerp candidate)
      (knp-integer-list-p values)
      (equal (len values)
             (len initial-values)))
     (knp-complete-loop-p
      values candidate last-index requested-length))))

(defun-sk knp-initial-array-p
    (values requested-length)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i requested-length))
     (equal (knp-nth values i) 0))))

;; The complete prime_numbers'vc proposition.  Every arrow below is retained
;; as an implication, including the two extensional update premises generated
;; by the source verification condition.

(defun knuth-prime-numbers-prime-numbersqtvc-statement-for-array-p
    (values requested-length)
  (let* ((after-two
          (knp-list-set values 0 2))
         (after-three
          (knp-list-set after-two 1 3))
         (last-index
          (- requested-length 1)))
    (and
     (<= 0 0)
     (< 0 (len values))
     (implies
      (equal (len after-two)
             (len values))
      (implies
       (knp-update-law-p
        after-two values 0 2)
       (and
        (<= 0 1)
        (< 1 (len after-two))
        (implies
         (equal (len after-three)
                (len after-two))
         (implies
          (knp-update-law-p
           after-three after-two 1 3)
          (and
           (implies
            (<= 2 (+ last-index 1))
            (and
             (knp-search-state-p
              after-three 2 5)
             (knp-all-loop-executions-p
              after-three
              last-index
              requested-length)))
           (implies
            (< (+ last-index 1) 2)
            (and
             (equal (len after-three)
                    requested-length)
             (knp-first-primes-p
              after-three
              requested-length))))))))))))

(defun-sk knp-array-obligation-p (requested-length)
  (forall (values)
    (implies
     (and
      (knp-integer-list-p values)
      (knp-initial-array-p
       values requested-length)
      (equal (len values)
             requested-length))
     (knuth-prime-numbers-prime-numbersqtvc-statement-for-array-p
      values requested-length))))

(defun knuth-prime-numbers-prime-numbersqtvc-statement
    (requested-length)
  (implies
   (and
    (knp-bertrand-postulate-p)
    (integerp requested-length)
    (<= 2 requested-length))
   (and
    (<= 0 requested-length)
    (knp-array-obligation-p requested-length))))

(value-triple :itpeval-statement-checked)
:q
