;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_a3:
;; the recursively defined integer sequence has 2005 consecutive
;; positive-indexed terms divisible by 2006. This file contains no proof.

(in-package "ACL2")

;; The source hypotheses uniquely determine every positive-indexed term.
;; Writing n=k+1 in the recurrence gives
;;
;;   x(n) = x(n-1) + x(n-2006)  for n > 2006.
;;
;; The Lean source additionally fixes x(0)=0, but that value is never used:
;; k-2005 is positive whenever k>=2006. The definition below is therefore
;; the common positive-indexed sequence from the Lean and Isabelle sources,
;; reduced modulo 2006. Reduction modulo 2006 commutes with the recurrence,
;; and a source term is divisible by 2006 exactly when this residue is zero.
(defun putnam-2006-a3-term-mod-2006 (n)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (natp n)) 0)
   ((zp n) 0)
   ((<= n 2006) (mod n 2006))
   (t
    (mod
     (+ (putnam-2006-a3-term-mod-2006 (- n 1))
        (putnam-2006-a3-term-mod-2006 (- n 2006)))
     2006))))

(defun putnam-2006-a3-divisible-block-p (start count)
  (declare (xargs :measure (nfix count)))
  (if (or (not (natp start))
          (not (natp count)))
      nil
    (if (zp count)
        t
      (and
       (equal (putnam-2006-a3-term-mod-2006 start) 0)
       (putnam-2006-a3-divisible-block-p
        (+ start 1) (- count 1))))))

(defun-sk putnam-2006-a3-divisible-block-exists-p ()
  (exists
   (start)
   (and
    (natp start)
    (< 0 start)
    (putnam-2006-a3-divisible-block-p start 2005))))

;; The positive starting index remains genuinely existential, exactly as in
;; the source. No periodicity bound or precomputed witness is part of the
;; statement.
(defun putnambench-putnam-2006-a3-statement ()
  (putnam-2006-a3-divisible-block-exists-p))

(value-triple :itpeval-statement-checked)
:q
