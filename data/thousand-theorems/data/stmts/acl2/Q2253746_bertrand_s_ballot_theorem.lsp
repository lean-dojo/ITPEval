;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q2253746, "Bertrand's ballot theorem": when
;; candidate A receives p votes and candidate B receives q votes with q < p,
;; the uniform probability that every nonempty suffix of the count has
;; positive A-minus-B sum is (p - q) / (p + q). This file contains no proof.

(in-package "ACL2")

;; These are exactly the lists of length n over the integer votes 1 and -1.
(defun q2253746-prepend-vote-to-each (vote sequences)
  (if (consp sequences)
      (cons (cons vote (car sequences))
            (q2253746-prepend-vote-to-each
             vote (cdr sequences)))
    nil))

(defun q2253746-vote-sequences (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list nil)
    (let ((shorter
           (q2253746-vote-sequences (- n 1))))
      (append
       (q2253746-prepend-vote-to-each 1 shorter)
       (q2253746-prepend-vote-to-each -1 shorter)))))

(defun q2253746-vote-list-p (votes)
  (if (consp votes)
      (and (or (equal (car votes) 1)
               (equal (car votes) -1))
           (q2253746-vote-list-p (cdr votes)))
    (equal votes nil)))

(defun q2253746-count-vote (vote votes)
  (if (consp votes)
      (+ (if (equal (car votes) vote) 1 0)
         (q2253746-count-vote vote (cdr votes)))
    0))

(defun q2253746-counted-sequence-p (votes p q)
  (and (q2253746-vote-list-p votes)
       (equal (q2253746-count-vote 1 votes) p)
       (equal (q2253746-count-vote -1 votes) q)))

(defun q2253746-integer-list-sum (values)
  (if (consp values)
      (+ (car values)
         (q2253746-integer-list-sum (cdr values)))
    0))

;; Recursing through the tails checks every nonempty suffix, matching
;; Ballot.staysPositive in the Lean source.
(defun q2253746-stays-positive-p (votes)
  (if (consp votes)
      (and (< 0 (q2253746-integer-list-sum votes))
           (q2253746-stays-positive-p (cdr votes)))
    (equal votes nil)))

(defun q2253746-count-all (sequences p q)
  (if (consp sequences)
      (+ (if (q2253746-counted-sequence-p
              (car sequences) p q)
             1
           0)
         (q2253746-count-all (cdr sequences) p q))
    0))

(defun q2253746-count-positive (sequences p q)
  (if (consp sequences)
      (+ (if (and
              (q2253746-counted-sequence-p
               (car sequences) p q)
              (q2253746-stays-positive-p
               (car sequences)))
             1
           0)
         (q2253746-count-positive
          (cdr sequences) p q))
    0))

(defun q2253746-all-countings (p q)
  (if (and (natp p) (natp q))
      (q2253746-count-all
       (q2253746-vote-sequences (+ p q)) p q)
    0))

(defun q2253746-positive-countings (p q)
  (if (and (natp p) (natp q))
      (q2253746-count-positive
       (q2253746-vote-sequences (+ p q)) p q)
    0))

(defun q2253746-uniform-positive-probability (p q)
  (let ((total (q2253746-all-countings p q)))
    (if (equal total 0)
        0
      (/ (q2253746-positive-countings p q)
         total))))

(defun thousand-theorems-q2253746-bertrands-ballot-theorem-statement
    (q p)
  (implies
   (and (natp q)
        (natp p)
        (< q p))
   (equal
    (q2253746-uniform-positive-probability p q)
    (/ (- p q) (+ p q)))))

(value-triple :itpeval-statement-checked)
:q
