;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__032, "The Four Color Problem": every finite simple
;; plane map, represented by a rational straight-line planar adjacency graph
;; of its regions, admits a proper coloring of adjacent regions with at most
;; four colors. This file contains no proof.

(in-package "ACL2")

;; A region record is (:region identifier x-coordinate y-coordinate), and a
;; border record is (:border first-region-id second-region-id).

(defun ht032-region-recordp (region)
  (and (true-listp region)
       (equal (len region) 4)
       (equal (nth 0 region) :region)
       (rationalp (nth 2 region))
       (rationalp (nth 3 region))))

(defun ht032-region-listp (regions)
  (if (consp regions)
      (and (ht032-region-recordp (car regions))
           (ht032-region-listp (cdr regions)))
    (equal regions nil)))

(defun ht032-region-id (region)
  (nth 1 region))

(defun ht032-region-x (region)
  (nth 2 region))

(defun ht032-region-y (region)
  (nth 3 region))

(defun ht032-region-identifiers (regions)
  (if (consp regions)
      (cons (ht032-region-id (car regions))
            (ht032-region-identifiers (cdr regions)))
    nil))

(defun ht032-region-coordinates (regions)
  (if (consp regions)
      (cons (cons (ht032-region-x (car regions))
                  (ht032-region-y (car regions)))
            (ht032-region-coordinates (cdr regions)))
    nil))

(defun ht032-orientation (a b c)
  (- (* (- (ht032-region-x b) (ht032-region-x a))
        (- (ht032-region-y c) (ht032-region-y a)))
     (* (- (ht032-region-y b) (ht032-region-y a))
        (- (ht032-region-x c) (ht032-region-x a)))))

(defun ht032-noncollinear-with-third-p (a b remaining)
  (if (consp remaining)
      (and (not (equal (ht032-orientation a b (car remaining)) 0))
           (ht032-noncollinear-with-third-p a b (cdr remaining)))
    t))

(defun ht032-noncollinear-with-pairs-p (a remaining)
  (if (consp remaining)
      (and (ht032-noncollinear-with-third-p
            a (car remaining) (cdr remaining))
           (ht032-noncollinear-with-pairs-p a (cdr remaining)))
    t))

(defun ht032-general-position-p (regions)
  (if (consp regions)
      (and (ht032-noncollinear-with-pairs-p
            (car regions) (cdr regions))
           (ht032-general-position-p (cdr regions)))
    t))

(defun ht032-border-recordp (border region-identifiers)
  (and (true-listp border)
       (equal (len border) 3)
       (equal (nth 0 border) :border)
       (member-equal (nth 1 border) region-identifiers)
       (member-equal (nth 2 border) region-identifiers)
       (not (equal (nth 1 border) (nth 2 border)))))

(defun ht032-border-listp (borders region-identifiers)
  (if (consp borders)
      (and (ht032-border-recordp (car borders) region-identifiers)
           (ht032-border-listp (cdr borders) region-identifiers))
    (equal borders nil)))

(defun ht032-border-first (border)
  (nth 1 border))

(defun ht032-border-second (border)
  (nth 2 border))

(defun ht032-same-undirected-border-p (left right)
  (or (and (equal (ht032-border-first left)
                  (ht032-border-first right))
           (equal (ht032-border-second left)
                  (ht032-border-second right)))
      (and (equal (ht032-border-first left)
                  (ht032-border-second right))
           (equal (ht032-border-second left)
                  (ht032-border-first right)))))

(defun ht032-border-distinct-from-list-p (border remaining)
  (if (consp remaining)
      (and (not (ht032-same-undirected-border-p border (car remaining)))
           (ht032-border-distinct-from-list-p border (cdr remaining)))
    t))

(defun ht032-no-duplicate-borders-p (borders)
  (if (consp borders)
      (and (ht032-border-distinct-from-list-p
            (car borders) (cdr borders))
           (ht032-no-duplicate-borders-p (cdr borders)))
    t))

(defun ht032-find-region (identifier regions)
  (if (consp regions)
      (if (equal identifier (ht032-region-id (car regions)))
          (car regions)
        (ht032-find-region identifier (cdr regions)))
    nil))

(defun ht032-strict-opposite-signs-p (left right)
  (or (and (< left 0) (< 0 right))
      (and (< right 0) (< 0 left))))

(defun ht032-proper-segment-crossing-p (left right regions)
  (let* ((a (ht032-find-region (ht032-border-first left) regions))
         (b (ht032-find-region (ht032-border-second left) regions))
         (c (ht032-find-region (ht032-border-first right) regions))
         (d (ht032-find-region (ht032-border-second right) regions)))
    (and
     (ht032-strict-opposite-signs-p
      (ht032-orientation a b c)
      (ht032-orientation a b d))
     (ht032-strict-opposite-signs-p
      (ht032-orientation c d a)
      (ht032-orientation c d b)))))

(defun ht032-border-noncrossing-with-list-p
    (border remaining regions)
  (if (consp remaining)
      (and (not (ht032-proper-segment-crossing-p
                 border (car remaining) regions))
           (ht032-border-noncrossing-with-list-p
            border (cdr remaining) regions))
    t))

(defun ht032-noncrossing-borders-p (borders regions)
  (if (consp borders)
      (and (ht032-border-noncrossing-with-list-p
            (car borders) (cdr borders) regions)
           (ht032-noncrossing-borders-p (cdr borders) regions))
    t))

(defun ht032-simple-plane-map-p (regions borders)
  (and
   (true-listp regions)
   (true-listp borders)
   (ht032-region-listp regions)
   (no-duplicatesp-equal (ht032-region-identifiers regions))
   (no-duplicatesp-equal (ht032-region-coordinates regions))
   (ht032-general-position-p regions)
   (ht032-border-listp borders (ht032-region-identifiers regions))
   (ht032-no-duplicate-borders-p borders)
   (ht032-noncrossing-borders-p borders regions)))

(defun ht032-color-differs-from-assigned-p
    (other-region color coloring)
  (let ((entry (assoc-equal other-region coloring)))
    (or (not (consp entry))
        (not (equal color (cdr entry))))))

(defun ht032-color-choice-compatible-with-borders-p
    (region color borders coloring)
  (if (consp borders)
      (and
       (cond
        ((equal region (ht032-border-first (car borders)))
         (ht032-color-differs-from-assigned-p
          (ht032-border-second (car borders)) color coloring))
        ((equal region (ht032-border-second (car borders)))
         (ht032-color-differs-from-assigned-p
          (ht032-border-first (car borders)) color coloring))
        (t t))
       (ht032-color-choice-compatible-with-borders-p
        region color (cdr borders) coloring))
    t))

(defun ht032-four-colorable-from-p
    (remaining-regions borders coloring)
  (declare (xargs :measure (len remaining-regions)))
  (if (consp remaining-regions)
      (let ((region (ht032-region-id (car remaining-regions))))
        (or
         (and
          (ht032-color-choice-compatible-with-borders-p
           region 0 borders coloring)
          (ht032-four-colorable-from-p
           (cdr remaining-regions)
           borders
           (cons (cons region 0) coloring)))
         (and
          (ht032-color-choice-compatible-with-borders-p
           region 1 borders coloring)
          (ht032-four-colorable-from-p
           (cdr remaining-regions)
           borders
           (cons (cons region 1) coloring)))
         (and
          (ht032-color-choice-compatible-with-borders-p
           region 2 borders coloring)
          (ht032-four-colorable-from-p
           (cdr remaining-regions)
           borders
           (cons (cons region 2) coloring)))
         (and
          (ht032-color-choice-compatible-with-borders-p
           region 3 borders coloring)
          (ht032-four-colorable-from-p
           (cdr remaining-regions)
           borders
           (cons (cons region 3) coloring)))))
    t))

(defun ht032-colorable-with-four-p (regions borders)
  (ht032-four-colorable-from-p regions borders nil))

(defun hundred-theorems-032-the-four-color-problem-statement
    (regions borders)
  (implies
   (ht032-simple-plane-map-p regions borders)
   (ht032-colorable-with-four-p regions borders)))

(value-triple :itpeval-statement-checked)
:q
