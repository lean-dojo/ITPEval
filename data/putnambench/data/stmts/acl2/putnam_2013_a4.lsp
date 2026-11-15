;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_a4:
;; balanced zero counts on equal-length arcs of a finite binary circle force
;; an arc realizing both integral average digit counts. This file contains no
;; proof.

(in-package "ACL2")

;; A natural below 2^N is the unique N-bit table for a function
;; Fin N -> Fin 2.  An arc is the two-element list (start length), with
;; start in Fin N and length in Fin (N+1).

(defun putnam-2013-a4-bit (circle-code position)
  (mod (floor circle-code (expt 2 position)) 2))

(defun putnam-2013-a4-arc-p (arc n)
  (and
   (true-listp arc)
   (equal (len arc) 2)
   (natp (nth 0 arc))
   (< (nth 0 arc) n)
   (natp (nth 1 arc))
   (<= (nth 1 arc) n)))

(defun putnam-2013-a4-all-arcs-p (arcs n)
  (if (endp arcs)
      t
    (and
     (putnam-2013-a4-arc-p (car arcs) n)
     (putnam-2013-a4-all-arcs-p (cdr arcs) n))))

(defun putnam-2013-a4-digit-count
    (circle-code n start length digit)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      0
    (let* ((offset (- length 1))
           (position (mod (+ start offset) n)))
      (+
       (if (equal
            (putnam-2013-a4-bit circle-code position)
            digit)
           1
         0)
       (putnam-2013-a4-digit-count
        circle-code n start offset digit)))))

(defun putnam-2013-a4-zero-count
    (circle-code n arc)
  (putnam-2013-a4-digit-count
   circle-code n (nth 0 arc) (nth 1 arc) 0))

(defun putnam-2013-a4-one-count
    (circle-code n arc)
  (putnam-2013-a4-digit-count
   circle-code n (nth 0 arc) (nth 1 arc) 1))

;; These nested recursions exhaust all pairs of starts for one fixed length.

(defun putnam-2013-a4-balanced-against-p
    (circle-code n length start other-count)
  (declare (xargs :measure (nfix other-count)))
  (if (zp other-count)
      t
    (let ((other (- other-count 1)))
      (and
       (<=
        (abs
         (-
          (putnam-2013-a4-digit-count
           circle-code n start length 0)
          (putnam-2013-a4-digit-count
           circle-code n other length 0)))
        1)
       (putnam-2013-a4-balanced-against-p
        circle-code n length start other)))))

(defun putnam-2013-a4-balanced-starts-p
    (circle-code n length start-count)
  (declare (xargs :measure (nfix start-count)))
  (if (zp start-count)
      t
    (let ((start (- start-count 1)))
      (and
       (putnam-2013-a4-balanced-against-p
        circle-code n length start n)
       (putnam-2013-a4-balanced-starts-p
        circle-code n length start)))))

(defun putnam-2013-a4-balanced-lengths-p
    (circle-code n length-count)
  (declare (xargs :measure (nfix length-count)))
  (if (zp length-count)
      t
    (let ((length (- length-count 1)))
      (and
       (putnam-2013-a4-balanced-starts-p
        circle-code n length n)
       (putnam-2013-a4-balanced-lengths-p
        circle-code n length)))))

(defun putnam-2013-a4-zero-sum
    (circle-code n arcs)
  (if (endp arcs)
      0
    (+
     (putnam-2013-a4-zero-count
      circle-code n (car arcs))
     (putnam-2013-a4-zero-sum
      circle-code n (cdr arcs)))))

(defun putnam-2013-a4-one-sum
    (circle-code n arcs)
  (if (endp arcs)
      0
    (+
     (putnam-2013-a4-one-count
      circle-code n (car arcs))
     (putnam-2013-a4-one-sum
      circle-code n (cdr arcs)))))

;; The source conclusion is existential.  The two searches below keep its
;; witness internal while ranging over every start and every permitted length.

(defun putnam-2013-a4-target-at-start-p
    (circle-code n k zero-total one-total length start-count)
  (declare (xargs :measure (nfix start-count)))
  (if (zp start-count)
      nil
    (let* ((start (- start-count 1))
           (arc (list start length)))
      (or
       (and
        (equal
         (* k
            (putnam-2013-a4-zero-count
             circle-code n arc))
         zero-total)
        (equal
         (* k
            (putnam-2013-a4-one-count
             circle-code n arc))
         one-total))
       (putnam-2013-a4-target-at-start-p
        circle-code n k zero-total one-total length start)))))

(defun putnam-2013-a4-target-arc-exists-p
    (circle-code n k zero-total one-total length-count)
  (declare (xargs :measure (nfix length-count)))
  (if (zp length-count)
      nil
    (let ((length (- length-count 1)))
      (or
       (putnam-2013-a4-target-at-start-p
        circle-code n k zero-total one-total length n)
       (putnam-2013-a4-target-arc-exists-p
        circle-code n k zero-total one-total length)))))

;; The source functions Z and N are uniquely fixed by their digit-count
;; equations, so they are unfolded above.  Likewise, the integer-valued
;; average parameters are eliminated definitionally: for positive K their
;; existence is exactly divisibility of the corresponding sums by K.

(defun putnambench-putnam-2013-a4-statement
    (n k circle-code selected-arcs)
  (let ((zero-total
         (putnam-2013-a4-zero-sum
          circle-code n selected-arcs))
        (one-total
         (putnam-2013-a4-one-sum
          circle-code n selected-arcs)))
    (implies
     (and
      (posp n)
      (posp k)
      (natp circle-code)
      (< circle-code (expt 2 n))
      (true-listp selected-arcs)
      (equal (len selected-arcs) k)
      (putnam-2013-a4-all-arcs-p selected-arcs n)
      (putnam-2013-a4-balanced-lengths-p
       circle-code n (+ n 1))
      (equal (mod zero-total k) 0)
      (equal (mod one-total k) 0))
     (putnam-2013-a4-target-arc-exists-p
      circle-code n k zero-total one-total (+ n 1)))))

(value-triple :itpeval-statement-checked)
:q
