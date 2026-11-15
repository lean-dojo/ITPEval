;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__030, "The Ballot Problem": for natural vote totals
;; p and q, the number of A/B vote sequences in which A is strictly ahead
;; after every vote satisfies the classical ballot counting identity relative
;; to all sequences with p votes for A and q votes for B. This file contains
;; no proof.

(in-package "ACL2")

(defun ht030-prepend-vote-to-each (vote sequences)
  (if (consp sequences)
      (cons (cons vote (car sequences))
            (ht030-prepend-vote-to-each vote (cdr sequences)))
    nil))

(defun ht030-vote-sequences (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list nil)
    (let ((shorter (ht030-vote-sequences (- n 1))))
      (append (ht030-prepend-vote-to-each :a shorter)
              (ht030-prepend-vote-to-each :b shorter)))))

(defun ht030-count-vote (vote votes)
  (if (consp votes)
      (+ (if (equal (car votes) vote) 1 0)
         (ht030-count-vote vote (cdr votes)))
    0))

(defun ht030-has-vote-totals-p (votes p q)
  (and (true-listp votes)
       (equal (ht030-count-vote :a votes) p)
       (equal (ht030-count-vote :b votes) q)))

(defun ht030-strictly-ahead-from-p (votes a-count b-count)
  (if (consp votes)
      (let* ((next-a (+ a-count
                        (if (equal (car votes) :a) 1 0)))
             (next-b (+ b-count
                        (if (equal (car votes) :b) 1 0))))
        (and (< next-b next-a)
             (ht030-strictly-ahead-from-p
              (cdr votes) next-a next-b)))
    t))

(defun ht030-strictly-ahead-p (votes)
  (and (true-listp votes)
       (ht030-strictly-ahead-from-p votes 0 0)))

(defun ht030-count-all-with-totals (sequences p q)
  (if (consp sequences)
      (+ (if (ht030-has-vote-totals-p (car sequences) p q)
             1
           0)
         (ht030-count-all-with-totals (cdr sequences) p q))
    0))

(defun ht030-count-valid-with-totals (sequences p q)
  (if (consp sequences)
      (+ (if (and (ht030-has-vote-totals-p
                   (car sequences) p q)
                  (ht030-strictly-ahead-p (car sequences)))
             1
           0)
         (ht030-count-valid-with-totals
          (cdr sequences) p q))
    0))

(defun ht030-all-countings (p q)
  (if (and (natp p) (natp q))
      (ht030-count-all-with-totals
       (ht030-vote-sequences (+ p q)) p q)
    0))

(defun ht030-valid-countings (p q)
  (if (and (natp p) (natp q))
      (ht030-count-valid-with-totals
       (ht030-vote-sequences (+ p q)) p q)
    0))

(defun ht030-natural-difference (p q)
  (if (and (natp p)
           (natp q)
           (<= q p))
      (- p q)
    0))

(defun hundred-theorems-030-the-ballot-problem-statement (p q)
  (implies
   (and (natp p)
        (natp q))
   (equal
    (* (+ p q)
       (ht030-valid-countings p q))
    (* (ht030-natural-difference p q)
       (ht030-all-countings p q)))))

(value-triple :itpeval-statement-checked)
:q
