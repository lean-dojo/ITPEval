;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_a4:
;; every bounded integer sequence satisfying the given exact fractional
;; four-term recurrence with nonzero denominators is eventually periodic.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A state (u_n u_(n+1) u_(n+2) u_(n+3)) has a unique successor under the
;; recurrence. Thus every source sequence is uniquely represented by its four
;; initial integers and the recursive orbit below, while every orbit satisfying
;; the integrality and nonzero-denominator conditions is a source sequence.

(defun putnam-1964-a4-denominator (quad)
  (+
   (* (cadddr quad) (caddr quad))
   (cadr quad)
   (car quad)))

(defun putnam-1964-a4-numerator (quad)
  (+
   (cadddr quad)
   (caddr quad)
   (* (cadr quad) (car quad))))

(defun putnam-1964-a4-next-state (quad)
  (list
   (cadr quad)
   (caddr quad)
   (cadddr quad)
   (/
    (putnam-1964-a4-numerator quad)
    (putnam-1964-a4-denominator quad))))

(defun putnam-1964-a4-orbit-state (initial-state steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      initial-state
    (putnam-1964-a4-next-state
     (putnam-1964-a4-orbit-state
      initial-state (- steps 1)))))

(defun putnam-1964-a4-orbit-value (initial-state n)
  (car
   (putnam-1964-a4-orbit-state initial-state n)))

(defun-sk putnam-1964-a4-orbit-bounded-by-p
    (initial-state lower upper)
  (forall (n)
    (implies
     (natp n)
     (let ((value
            (putnam-1964-a4-orbit-value initial-state n)))
       (and
        (integerp value)
        (<= lower value)
        (<= value upper))))))

(defun-sk putnam-1964-a4-bounded-integer-orbit-p
    (initial-state)
  (exists (lower upper)
    (and
     (integerp lower)
     (integerp upper)
     (putnam-1964-a4-orbit-bounded-by-p
      initial-state lower upper))))

(defun-sk putnam-1964-a4-nonzero-denominators-p
    (initial-state)
  (forall (n)
    (implies
     (natp n)
     (not
      (equal
       (putnam-1964-a4-denominator
        (putnam-1964-a4-orbit-state initial-state n))
       0)))))

(defun-sk putnam-1964-a4-periodic-tail-p
    (initial-state cutoff period)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (equal
      (putnam-1964-a4-orbit-value
       initial-state (+ n period))
      (putnam-1964-a4-orbit-value initial-state n)))))

(defun-sk putnam-1964-a4-eventually-periodic-p
    (initial-state)
  (exists (cutoff period)
    (and
     (natp cutoff)
     (posp period)
     (putnam-1964-a4-periodic-tail-p
      initial-state cutoff period))))

(defun-sk putnambench-putnam-1964-a4-statement ()
  (forall (u0 u1 u2 u3)
    (implies
     (and
      (integerp u0)
      (integerp u1)
      (integerp u2)
      (integerp u3))
     (let ((initial-state (list u0 u1 u2 u3)))
       (implies
        (and
         (putnam-1964-a4-bounded-integer-orbit-p
          initial-state)
         (putnam-1964-a4-nonzero-denominators-p
          initial-state))
        (putnam-1964-a4-eventually-periodic-p
         initial-state))))))

(value-triple :itpeval-statement-checked)
:q
