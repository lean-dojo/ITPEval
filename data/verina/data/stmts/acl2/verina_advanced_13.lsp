;; Statement-only formalization of VERINA corpus artifact verina_advanced_13,
;; "hasChordIntersection": a deterministic normalization, insertion sort, and
;; stack scan detects whether any two circle chords have alternating endpoints,
;; together with its correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-13-nat-list-p (xs)
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-13-nat-list-p (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-13-nat-list-list-p (xss)
  (if (consp xss)
      (and
       (verina-advanced-13-nat-list-p (car xss))
       (verina-advanced-13-nat-list-list-p (cdr xss)))
    (equal xss nil)))

(defun verina-advanced-13-list-length (xs)
  (if (consp xs)
      (+ 1 (verina-advanced-13-list-length (cdr xs)))
    0))

;; These are the source List.get! operations at indices zero and one, whose
;; default value for Nat is zero.

(defun verina-advanced-13-endpoint-zero (chord)
  (if (consp chord)
      (car chord)
    0))

(defun verina-advanced-13-endpoint-one (chord)
  (if (and (consp chord)
           (consp (cdr chord)))
      (car (cdr chord))
    0))

(defun verina-advanced-13-flatten (xss)
  (if (consp xss)
      (append
       (car xss)
       (verina-advanced-13-flatten (cdr xss)))
    nil))

(defun verina-advanced-13-valid-chord-p (chord n)
  (let ((a (verina-advanced-13-endpoint-zero chord))
        (b (verina-advanced-13-endpoint-one chord)))
    (and
     (equal (verina-advanced-13-list-length chord) 2)
     (<= 1 a)
     (<= a (* 2 n))
     (<= 1 b)
     (<= b (* 2 n)))))

(defun verina-advanced-13-all-valid-chords-p (chords n)
  (if (consp chords)
      (and
       (verina-advanced-13-valid-chord-p (car chords) n)
       (verina-advanced-13-all-valid-chords-p (cdr chords) n))
    (equal chords nil)))

(defun verina-advanced-13-has-chord-intersection-precond
    (n chords)
  (and
   (natp n)
   (verina-advanced-13-nat-list-list-p chords)
   (<= 2 n)
   (equal (verina-advanced-13-list-length chords) n)
   (verina-advanced-13-all-valid-chords-p chords n)
   (no-duplicatesp-equal
    (verina-advanced-13-flatten chords))))

(defun verina-advanced-13-normalize-chord (chord)
  (let ((a (verina-advanced-13-endpoint-zero chord))
        (b (verina-advanced-13-endpoint-one chord)))
    (if (< b a)
        (list b a)
      (list a b))))

(defun verina-advanced-13-normalize-chords (chords)
  (if (consp chords)
      (cons
       (verina-advanced-13-normalize-chord (car chords))
       (verina-advanced-13-normalize-chords (cdr chords)))
    nil))

(defun verina-advanced-13-drop-stack-before (a stack)
  (if (consp stack)
      (if (< (verina-advanced-13-endpoint-one (car stack)) a)
          (verina-advanced-13-drop-stack-before a (cdr stack))
        stack)
    nil))

(defun verina-advanced-13-check-intersection
    (stack remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((chord (car remaining))
             (rest (cdr remaining))
             (a (verina-advanced-13-endpoint-zero chord))
             (b (verina-advanced-13-endpoint-one chord))
             (new-stack
              (verina-advanced-13-drop-stack-before a stack)))
        (if (consp new-stack)
            (let ((top-end
                   (verina-advanced-13-endpoint-one
                    (car new-stack))))
              (if (and (< a top-end)
                       (< top-end b))
                  t
                (verina-advanced-13-check-intersection
                 (cons chord new-stack)
                 rest)))
          (verina-advanced-13-check-intersection
           (cons chord new-stack)
           rest)))
    nil))

(defun verina-advanced-13-insert-chord (x xs)
  (if (consp xs)
      (let ((y (car xs)))
        (if (< (verina-advanced-13-endpoint-zero x)
               (verina-advanced-13-endpoint-zero y))
            (cons x xs)
          (cons
           y
           (verina-advanced-13-insert-chord x (cdr xs)))))
    (list x)))

(defun verina-advanced-13-sort-chords (xs)
  (if (consp xs)
      (verina-advanced-13-insert-chord
       (car xs)
       (verina-advanced-13-sort-chords (cdr xs)))
    nil))

(defun verina-advanced-13-has-chord-intersection
    (n chords)
  (declare (ignore n))
  (verina-advanced-13-check-intersection
   nil
   (verina-advanced-13-sort-chords
    (verina-advanced-13-normalize-chords chords))))

(defun verina-advanced-13-chords-intersect-p
    (chord1 chord2)
  (let ((a1 (verina-advanced-13-endpoint-zero chord1))
        (b1 (verina-advanced-13-endpoint-one chord1))
        (a2 (verina-advanced-13-endpoint-zero chord2))
        (b2 (verina-advanced-13-endpoint-one chord2)))
    (or
     (and (< a1 a2)
          (< a2 b1)
          (< b1 b2))
     (and (< a2 a1)
          (< a1 b2)
          (< b2 b1)))))

(defun verina-advanced-13-any-intersection-with-p
    (chord chords)
  (if (consp chords)
      (or
       (verina-advanced-13-chords-intersect-p
        chord (car chords))
       (verina-advanced-13-any-intersection-with-p
        chord (cdr chords)))
    nil))

;; This is the source checkAllPairs helper, retained even though the source
;; postcondition states its two directions through Pairwise and nested any.

(defun verina-advanced-13-check-all-pairs (chords)
  (if (consp chords)
      (if (verina-advanced-13-any-intersection-with-p
           (car chords) (cdr chords))
          t
        (verina-advanced-13-check-all-pairs (cdr chords)))
    nil))

(defun verina-advanced-13-pairwise-nonintersection-with-p
    (chord chords)
  (if (consp chords)
      (and
       (not
        (verina-advanced-13-chords-intersect-p
         chord (car chords)))
       (verina-advanced-13-pairwise-nonintersection-with-p
        chord (cdr chords)))
    (equal chords nil)))

(defun verina-advanced-13-pairwise-nonintersection-p (chords)
  (if (consp chords)
      (and
       (verina-advanced-13-pairwise-nonintersection-with-p
        (car chords) (cdr chords))
       (verina-advanced-13-pairwise-nonintersection-p
        (cdr chords)))
    (equal chords nil)))

(defun verina-advanced-13-any-intersection-p
    (remaining whole)
  (if (consp remaining)
      (or
       (verina-advanced-13-any-intersection-with-p
        (car remaining) whole)
       (verina-advanced-13-any-intersection-p
        (cdr remaining) whole))
    nil))

(defun verina-advanced-13-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-13-has-chord-intersection-postcond
    (n chords result)
  (declare (ignore n))
  (let ((normalized
         (verina-advanced-13-normalize-chords chords)))
    (and
     (verina-advanced-13-bool-p result)
     (implies
      (verina-advanced-13-pairwise-nonintersection-p
       normalized)
      (not result))
     (implies
      (verina-advanced-13-any-intersection-p
       normalized normalized)
      result))))

(defun
    verina-advanced-13-has-chord-intersection-spec-satisfied-statement
    (n chords)
  (implies
   (verina-advanced-13-has-chord-intersection-precond
    n chords)
   (verina-advanced-13-has-chord-intersection-postcond
    n
    chords
    (verina-advanced-13-has-chord-intersection
     n chords))))

(value-triple :itpeval-statement-checked)
:q
