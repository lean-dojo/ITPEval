;; Statement-only formalization of VERINA corpus artifact verina_advanced_55,
;; "mostFrequent": the deterministic frequency-map program returns a
;; maximum-frequency integer, breaking ties by first occurrence in the
;; original nonempty list. This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-55-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-55-integer-listp (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-55-most-frequent-precond (xs)
  (not (equal xs nil)))

;; A frequency map is represented extensionally by an association list whose
;; entries are dotted pairs (key . count). Lookup with default zero is the
;; source HashMap.getD operation.

(defun verina-advanced-55-map-get-count (key frequency-map)
  (declare (xargs :measure (acl2-count frequency-map)))
  (if (consp frequency-map)
      (if (equal key (car (car frequency-map)))
          (cdr (car frequency-map))
        (verina-advanced-55-map-get-count
         key
         (cdr frequency-map)))
    0))

;; Updating the unique entry for KEY is extensionally the source
;; HashMap.insert operation.

(defun verina-advanced-55-map-insert-count
    (key count frequency-map)
  (declare (xargs :measure (acl2-count frequency-map)))
  (if (consp frequency-map)
      (if (equal key (car (car frequency-map)))
          (cons
           (cons key count)
           (cdr frequency-map))
        (cons
         (car frequency-map)
         (verina-advanced-55-map-insert-count
          key
          count
          (cdr frequency-map))))
    (list (cons key count))))

;; This tail recursion is List.foldl STEP over XS with the empty map, where
;; STEP increments the current count of each integer.

(defun verina-advanced-55-count-map-fold
    (remaining frequency-map)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((x (car remaining))
             (current
              (verina-advanced-55-map-get-count
               x
               frequency-map))
             (updated
              (verina-advanced-55-map-insert-count
               x
               (+ current 1)
               frequency-map)))
        (verina-advanced-55-count-map-fold
         (cdr remaining)
         updated))
    frequency-map))

(defun verina-advanced-55-count-map (xs)
  (verina-advanced-55-count-map-fold xs nil))

;; Taking the maximum is independent of map-enumeration order, so this fold
;; over the association-list representation is observationally identical to
;; folding maximum over HashMap.toList from initial value zero.

(defun verina-advanced-55-get-max-frequency (frequency-map)
  (declare (xargs :measure (acl2-count frequency-map)))
  (if (consp frequency-map)
      (let ((current-count (cdr (car frequency-map))))
        (let ((rest-maximum
               (verina-advanced-55-get-max-frequency
                (cdr frequency-map))))
          (if (> current-count rest-maximum)
              current-count
            rest-maximum)))
    0))

;; This is the set of keys selected by filtering HashMap.toList for entries
;; whose count equals MAX-FREQUENCY and then projecting their keys. Its order
;; may reflect the target map representation, but the program observes it only
;; through membership.

(defun verina-advanced-55-get-candidates
    (frequency-map max-frequency)
  (declare (xargs :measure (acl2-count frequency-map)))
  (if (consp frequency-map)
      (let ((entry (car frequency-map)))
        (if (equal (cdr entry) max-frequency)
            (cons
             (car entry)
             (verina-advanced-55-get-candidates
              (cdr frequency-map)
              max-frequency))
          (verina-advanced-55-get-candidates
           (cdr frequency-map)
           max-frequency)))
    nil))

;; Scanning XS and testing candidate membership is List.find?. The zero branch
;; is the source default when no candidate is found.

(defun verina-advanced-55-get-first-with-freq
    (xs candidates)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (member-equal (car xs) candidates)
          (car xs)
        (verina-advanced-55-get-first-with-freq
         (cdr xs)
         candidates))
    0))

;; The proof-valued nonempty-list argument is computationally erased. All
;; executable helpers and their data flow otherwise match the source program.

(defun verina-advanced-55-most-frequent (xs)
  (let* ((frequency-map
          (verina-advanced-55-count-map xs))
         (max-frequency
          (verina-advanced-55-get-max-frequency
           frequency-map))
         (candidates
          (verina-advanced-55-get-candidates
           frequency-map
           max-frequency)))
    (verina-advanced-55-get-first-with-freq
     xs
     candidates)))

;; This is List.countP with integer equality.

(defun verina-advanced-55-count-equal (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+
       (if (equal (car xs) value) 1 0)
       (verina-advanced-55-count-equal
        value
        (cdr xs)))
    0))

;; This is xs.all (fun x => count x <= count result).

(defun verina-advanced-55-all-counts-at-most-p
    (remaining xs result-count)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (<=
        (verina-advanced-55-count-equal
         (car remaining)
         xs)
        result-count)
       (verina-advanced-55-all-counts-at-most-p
        (cdr remaining)
        xs
        result-count))
    t))

;; This scan is equivalent to requiring that the head of XS filtered to
;; elements with RESULT-COUNT occurrences is SOME RESULT. It returns false
;; when the filtered list is empty.

(defun verina-advanced-55-first-with-result-count-p
    (remaining xs result result-count)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal
           (verina-advanced-55-count-equal
            (car remaining)
            xs)
           result-count)
          (equal (car remaining) result)
        (verina-advanced-55-first-with-result-count-p
         (cdr remaining)
         xs
         result
         result-count))
    nil))

(defun verina-advanced-55-most-frequent-postcond
    (xs result)
  (let ((result-count
         (verina-advanced-55-count-equal result xs)))
    (and
     (verina-advanced-55-integer-listp xs)
     (integerp result)
     (member-equal result xs)
     (verina-advanced-55-all-counts-at-most-p
      xs
      xs
      result-count)
     (verina-advanced-55-first-with-result-count-p
      xs
      xs
      result
      result-count))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and nonempty-list precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-55-most-frequent-spec-satisfied-statement
    (xs)
  (implies
   (and
    (verina-advanced-55-integer-listp xs)
    (verina-advanced-55-most-frequent-precond xs))
   (verina-advanced-55-most-frequent-postcond
    xs
    (verina-advanced-55-most-frequent xs))))

(value-triple :itpeval-statement-checked)
:q
