;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_b2:
;; the least positive starting integer whose 2017 consecutive positive
;; integers have no other representation length greater than one is 16.
;; This file contains no proof.

(in-package "ACL2")

(defun putnam-2017-b2-consecutive-sum (a k)
  (+ (* k a)
     (/ (* k (- k 1)) 2)))

;; For natural K > 1, N is a sum of K consecutive positive integers exactly
;; when N - K*(K-1)/2 is a positive multiple of K.
(defun putnam-2017-b2-representable-at-length-p (n k)
  (and (integerp n)
       (natp k)
       (< 1 k)
       (let ((remainder
              (- n (/ (* k (- k 1)) 2))))
         (and (< 0 remainder)
              (equal (mod remainder k) 0)))))

;; If positive N has a representation of length K, then K <= N. Thus this
;; descent checks every source length greater than one, without bounding the
;; theorem's arbitrary integer N or replacing its quantifiers by a finite
;; carrier.
(defun putnam-2017-b2-no-other-length-through-p (n k)
  (declare (xargs :measure (nfix k)))
  (if (and (integerp k)
           (< 1 k))
      (and
       (or (equal k 2017)
           (not
            (putnam-2017-b2-representable-at-length-p n k)))
       (putnam-2017-b2-no-other-length-through-p
        n (- k 1)))
    t))

(defun putnam-2017-b2-valid-start-p (a)
  (and
   (integerp a)
   (< 0 a)
   (let ((n (putnam-2017-b2-consecutive-sum a 2017)))
     (and
      (integerp n)
      (< 0 n)
      (putnam-2017-b2-no-other-length-through-p n n)))))

;; ACL2 universally closes A. The first conjunct says that 16 is valid, and
;; the second says that every valid positive integer start is at least 16;
;; together these are exactly the source least-element statement.
(defun putnambench-putnam-2017-b2-statement (a)
  (and
   (putnam-2017-b2-valid-start-p 16)
   (implies
    (putnam-2017-b2-valid-start-p a)
    (<= 16 a))))

(value-triple :itpeval-statement-checked)
:q
