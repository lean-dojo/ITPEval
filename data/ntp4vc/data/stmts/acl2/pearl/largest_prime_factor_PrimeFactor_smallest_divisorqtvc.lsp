;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/largest_prime_factor_PrimeFactor_smallest_divisorqtvc: the
;; smallest-divisor verification condition, including recursive-call progress
;; and the minimal-divisor specification for every possible result. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This is integer divisibility on the full source domain, with the quotient
;; witness kept internal to the relation.

(defun-sk lpfsd-divides-p (divisor dividend)
  (exists (quotient)
    (and
     (integerp divisor)
     (integerp dividend)
     (integerp quotient)
     (equal dividend (* divisor quotient)))))

;; The source invariant says that no integer in [2, upper) divides n.

(defun-sk lpfsd-no-smaller-divisor-p (n upper)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 2 i)
      (< i upper))
     (not (lpfsd-divides-p i n)))))

;; Under the source assumptions n and d are positive, so ACL2 MOD agrees with
;; the pinned Why3 remainder at this test. ACL2 T and NIL represent the two
;; source Boolean values.

(defun lpfsd-divisibility-test-value (n d)
  (if (<= 2 d)
      (if (equal (mod n d) 0) t nil)
    nil))

(defun lpfsd-next-divisor-vc-p (n d)
  (let ((o3 (+ d 1)))
    (and
     (and
      (<= 0 (- n d))
      (< (- n o3) (- n d)))
     (<= 2 n)
     (and
      (<= 2 o3)
      (<= o3 n))
     (lpfsd-no-smaller-divisor-p n o3))))

;; This preserves the universal Boolean continuation in the first VC conjunct.

(defun-sk lpfsd-all-false-tests-p (n d)
  (forall (o2)
    (implies
     (booleanp o2)
     (implies
      (equal o2 (lpfsd-divisibility-test-value n d))
      (implies
       (not (equal o2 t))
       (lpfsd-next-divisor-vc-p n d))))))

(defun lpfsd-progress-vc-p (n d)
  (let ((o1 (* d d)))
    (implies
     (not (< n o1))
     (and
      (implies
       (<= 2 d)
       (not (equal d 0)))
      (lpfsd-all-false-tests-p n d)))))

(defun lpfsd-result-spec-p (n d result)
  (and
   (and
    (<= d result)
    (<= result n))
   (lpfsd-divides-p result n)
   (lpfsd-no-smaller-divisor-p n result)))

;; The Boolean witness remains existential and internal to the recursive-result
;; premise, as in the pinned Why3 verification condition.

(defun-sk lpfsd-recursive-result-premise-p (n d result)
  (exists (o2)
    (and
     (booleanp o2)
     (equal o2 (lpfsd-divisibility-test-value n d))
     (if (equal o2 t)
         (equal result d)
       (and
        (and
         (<= (+ d 1) result)
         (<= result n))
        (lpfsd-divides-p result n)
        (lpfsd-no-smaller-divisor-p n result))))))

(defun lpfsd-result-premise-p (n d result)
  (let ((o1 (* d d)))
    (if (< n o1)
        (equal result n)
      (lpfsd-recursive-result-premise-p
       n d result))))

(defun-sk lpfsd-all-results-p (n d)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (lpfsd-result-premise-p n d result)
      (lpfsd-result-spec-p n d result)))))

(defun
  ntp4vc-pearl-largest-prime-factor-primefactor-smallest-divisorqtvc-statement
  (n d)
  (implies
   (and
    (integerp n)
    (integerp d)
    (<= 2 n)
    (<= 2 d)
    (<= d n)
    (lpfsd-no-smaller-divisor-p n d))
   (and
    (lpfsd-progress-vc-p n d)
    (lpfsd-all-results-p n d))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
