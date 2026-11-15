;; Statement-only formalization of VERINA corpus artifact verina_advanced_15,
;; "increasingTriplet": a deterministic two-threshold scan decides whether an
;; integer list contains indices i < j < k with increasing values.
;; This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-15-integer-listp (nums)
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-15-integer-listp (cdr nums)))
    (equal nums nil)))

;; The source precondition is True; the List Int domain is explicit in the
;; final correctness statement.

(defun verina-advanced-15-increasing-triplet-precond (nums)
  (declare (ignore nums))
  t)

(defun verina-advanced-15-list-length (nums)
  (if (consp nums)
      (+ 1 (verina-advanced-15-list-length (cdr nums)))
    0))

;; Option Int is represented by :none or by the tagged pair (:some . value).

(defun verina-advanced-15-some (value)
  (cons :some value))

(defun verina-advanced-15-loop
    (xs first-option second-option)
  (if (consp xs)
      (let ((x (car xs))
            (rest (cdr xs)))
        (if (equal first-option :none)
            (verina-advanced-15-loop
             rest
             (verina-advanced-15-some x)
             :none)
          (let ((first-value (cdr first-option)))
            (if (<= x first-value)
                (verina-advanced-15-loop
                 rest
                 (verina-advanced-15-some x)
                 second-option)
              (if (equal second-option :none)
                  (verina-advanced-15-loop
                   rest
                   first-option
                   (verina-advanced-15-some x))
                (let ((second-value (cdr second-option)))
                  (if (<= x second-value)
                      (verina-advanced-15-loop
                       rest
                       first-option
                       (verina-advanced-15-some x))
                    t)))))))
    nil))

(defun verina-advanced-15-increasing-triplet (nums)
  (if (< (verina-advanced-15-list-length nums) 3)
      nil
    (verina-advanced-15-loop nums :none :none)))

;; Each zip-index entry is the pair (value . zero-based-index), matching
;; List.zipIdx on the source list.

(defun verina-advanced-15-zip-index-from (nums index)
  (if (consp nums)
      (cons
       (cons (car nums) index)
       (verina-advanced-15-zip-index-from
        (cdr nums) (+ index 1)))
    nil))

(defun verina-advanced-15-zip-index (nums)
  (verina-advanced-15-zip-index-from nums 0))

(defun verina-advanced-15-any-third-p
    (first-entry second-entry entries)
  (if (consp entries)
      (let ((third-entry (car entries)))
        (or
         (and
          (< (cdr first-entry) (cdr second-entry))
          (< (cdr second-entry) (cdr third-entry))
          (< (car first-entry) (car second-entry))
          (< (car second-entry) (car third-entry)))
         (verina-advanced-15-any-third-p
          first-entry second-entry (cdr entries))))
    nil))

(defun verina-advanced-15-any-second-p
    (first-entry entries all-entries)
  (if (consp entries)
      (or
       (verina-advanced-15-any-third-p
        first-entry (car entries) all-entries)
       (verina-advanced-15-any-second-p
        first-entry (cdr entries) all-entries))
    nil))

(defun verina-advanced-15-any-increasing-triplet-p
    (entries all-entries)
  (if (consp entries)
      (or
       (verina-advanced-15-any-second-p
        (car entries) all-entries all-entries)
       (verina-advanced-15-any-increasing-triplet-p
        (cdr entries) all-entries))
    nil))

(defun verina-advanced-15-all-thirds-fail-p
    (first-entry second-entry entries)
  (if (consp entries)
      (let ((third-entry (car entries)))
        (and
         (or
          (<= (cdr second-entry) (cdr first-entry))
          (<= (cdr third-entry) (cdr second-entry))
          (<= (car second-entry) (car first-entry))
          (<= (car third-entry) (car second-entry)))
         (verina-advanced-15-all-thirds-fail-p
          first-entry second-entry (cdr entries))))
    (equal entries nil)))

(defun verina-advanced-15-all-seconds-fail-p
    (first-entry entries all-entries)
  (if (consp entries)
      (and
       (verina-advanced-15-all-thirds-fail-p
        first-entry (car entries) all-entries)
       (verina-advanced-15-all-seconds-fail-p
        first-entry (cdr entries) all-entries))
    (equal entries nil)))

(defun verina-advanced-15-all-triplets-fail-p
    (entries all-entries)
  (if (consp entries)
      (and
       (verina-advanced-15-all-seconds-fail-p
        (car entries) all-entries all-entries)
       (verina-advanced-15-all-triplets-fail-p
        (cdr entries) all-entries))
    (equal entries nil)))

(defun verina-advanced-15-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-15-increasing-triplet-postcond
    (nums result)
  (let ((indexed-nums
         (verina-advanced-15-zip-index nums)))
    (and
     (verina-advanced-15-integer-listp nums)
     (verina-advanced-15-bool-p result)
     (implies
      result
      (verina-advanced-15-any-increasing-triplet-p
       indexed-nums indexed-nums))
     (implies
      (not result)
      (verina-advanced-15-all-triplets-fail-p
       indexed-nums indexed-nums)))))

(defun
    verina-advanced-15-increasing-triplet-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-15-integer-listp nums)
    (verina-advanced-15-increasing-triplet-precond nums))
   (verina-advanced-15-increasing-triplet-postcond
    nums
    (verina-advanced-15-increasing-triplet nums))))

(value-triple :itpeval-statement-checked)
:q
