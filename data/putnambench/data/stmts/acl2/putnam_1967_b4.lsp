;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1967_b4: after successively toggling lockers whose numbers are
;; multiples of each operation number, exactly the perfect-square-numbered
;; lockers are open. This file contains no proof.

(in-package "ACL2")

;; On operations 0,...,n and locker indices 1,...,n, the source hypotheses
;; uniquely determine every locker value from the initially closed state.
;; The recursive function below definitionally eliminates that arbitrary
;; source function without changing its universally quantified conclusion.
;; Free n and i supply the source universal quantifiers.
;;
;; For positive i, an integer j satisfies j^2 = i exactly when a natural
;; candidate from 0 through i does, so the bounded search preserves the
;; source's internal existential integer witness.

(defun putnam-1967-b4-locker-open-after-p (operation locker)
  (declare (xargs :measure (nfix operation)))
  (if (zp operation)
      nil
    (let ((previous
           (putnam-1967-b4-locker-open-after-p
            (- operation 1) locker)))
      (if (equal (mod locker operation) 0)
          (not previous)
        previous))))

(defun putnam-1967-b4-square-witness-through-p (i candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (equal i 0)
    (or (equal (* candidate candidate) i)
        (putnam-1967-b4-square-witness-through-p
         i (- candidate 1)))))

(defun putnam-1967-b4-perfect-square-p (i)
  (and (natp i)
       (putnam-1967-b4-square-witness-through-p i i)))

(defun putnambench-putnam-1967-b4-statement (n i)
  (implies
   (and (natp n)
        (<= 1 n)
        (natp i)
        (<= 1 i)
        (<= i n))
   (equal
    (putnam-1967-b4-locker-open-after-p n i)
    (putnam-1967-b4-perfect-square-p i))))

(value-triple :itpeval-statement-checked)
:q
