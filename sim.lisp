; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defmacro match-let* (binds body)
  "Parallels racket's match-let* macro, using case-match."
  (case-match binds
    ('() body)
    (((pat val) . rst)
     ;; Case-match doesn't allow expressions for 'binds', so we bind
     ;; to 'greatbadness'. You should expect great badness if you name
     ;; your variable 'greatbadness'.
     `(let ((greatbadness ,val))
	(case-match greatbadness
	  (,pat (match-let* ,rst ,body)))))))

;; ---- Definitions ----

;; Represents the state of the sender, holding the data to send and the current sequence number.
(defdata sender-state `(sendstate ,tl ,nat))

;; Represents the state of the receiver, holding the data received so far.
(defdata receiver-state `(recvstate ,tl ,nat))

;; An event is one of:
;; - OK 	  both the packet and ack are transmitted.
;; - DROP-ACK     the packet is trasmitted but the ack is dropped.
;; - DROP-PACKET  the packet is dropped, no packet to ack.
(defdata event (enum '(ok drop-ack drop-packet)))

;; Represents a sequence of events that occur in the simulated network environment.
(defdata event-deck (listof event))

;; Represents the state of the simulation, holding the state of sender and receiver.
(defdata sim-state `(sim-state ,sender-state ,receiver-state))

;; ---- Functions ----

(definec simulator-completep (sim :sim-state) :bool
  "If the sender's sequence number larger than the data, there's no more data to send."
  (match-let* ((('sim-state sender-state &) sim)
	       (('sendstate data seq-num) sender-state))
    (not (> (len data) seq-num))))

(definec simulator-step (sim :sim-state event :event) :sim-state
  "Performs one round of the simulation with the given event."
  (if (simulator-completep sim) sim
    (match-let* ((('sim-state ('sendstate sdata sseq) ('recvstate rdata &)) sim))
      (cond
       ;; Packet dropped
       ((== event 'drop-packet) sim)
       ;; OK packet, sender up-to-date
       ((and (== event 'ok) (== sseq (len rdata)))
	`(sim-state (sendstate ,sdata ,(1+ sseq))
		    (recvstate ,(app rdata (list (nth sseq sdata))) 0)))
       ;; OK packet, sender is behind 
       ((and (== event 'ok) (!= sseq (len rdata)))
	`(sim-state (sendstate ,sdata ,(len rdata))
		    (recvstate ,rdata 0)))
       ;; Ack dropped, sender up-to-date
       ((and (== event 'drop-ack) (== sseq (len rdata)))
	`(sim-state (sendstate ,sdata ,sseq)
		    (recvstate ,(app rdata (list (nth sseq sdata))) 0)))
       ;; Ack dropped, sender behind
       ((and (== event 'drop-ack) (!= sseq (len rdata))) sim)))))

;; Nothing to send => nothing happens.
(check= (simulator-step
	 '(sim-state (sendstate nil 0)
		     (recvstate nil 0)) 'ok)
	'(sim-state (sendstate nil 0)
		    (recvstate nil 0)))

;; OK packet, sender up-to-date => receiver accepts packet, sender increments seq num.
(check= (simulator-step
	 '(sim-state (sendstate (1 2) 0)
		     (recvstate nil 0)) 'ok)
	'(sim-state (sendstate (1 2) 1)
		    (recvstate (1) 0)))

;; OK packet, sender is behind => receiver rejects packet, sender matches receiver's seq num. 
(check= (simulator-step
	 '(sim-state (sendstate (1 2) 0)
		     (recvstate (1) 0)) 'ok)
	'(sim-state (sendstate (1 2) 1)
		    (recvstate (1) 0)))

;; Ack dropped, sender up-to-date => receiver accepts packet, sender's seq num unchanged.
(check= (simulator-step
	 '(sim-state (sendstate (1 2) 0)
		     (recvstate () 0)) 'drop-ack)
	'(sim-state (sendstate (1 2) 0)
		    (recvstate (1) 0)))

;; Ack dropped, sender behind => nothing happens.
(check= (simulator-step
	 '(sim-state (sendstate (1 2) 0)
		     (recvstate (1) 0)) 'drop-ack)
	'(sim-state (sendstate (1 2) 0)
		    (recvstate (1) 0)))

;; Packet dropped => nothing happens.
(check= (simulator-step
	 '(sim-state (sendstate (1 2) 1)
		     (recvstate (1) 0)) 'drop-packet)
	'(sim-state (sendstate (1 2) 1)
		    (recvstate (1) 0)))


(definec simulator (sim :sim-state steps :event-deck) :sim-state
  "Repeatedly applies simulator-step with the events specified."
  :function-contract-strictp nil
  :body-contracts-strictp nil
  :skip-tests t
  (cond
   ((lendp steps) sim)
   (T (simulator-step (simulator sim (cdr steps)) (car steps)))))

(check= (simulator '(sim-state (sendstate () 0)
			       (recvstate () 0))
		   '())
	'(sim-state (sendstate () 0)
		    (recvstate () 0)))

(check= (simulator '(sim-state (sendstate (1 2 3) 0)
			       (recvstate () 0))
		   '(ok ok ok))
	'(sim-state (sendstate (1 2 3) 3)
		    (recvstate (1 2 3) 0)))

(check= (simulator '(sim-state (sendstate (1 2 3) 0)
			       (recvstate () 0))
		   '(ok drop-packet drop-ack ok))
	'(sim-state (sendstate (1 2 3) 2)
		    (recvstate (1 2) 0)))

;; `simulator` times out trying to prove the function contract during
;; definition, but this lemma passes fine.
(defthm simulator-function-contract
  (implies (and (sim-statep sim)
		(event-deckp evt))
	   (sim-statep (simulator sim evt))))

(verify-guards simulator)

;; ---- Proofs ----

(definec prefixp (x :tl y :tl) :bool
  "Checks if X is a prefix of Y."
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

(definec rs-prefix-of-ssp (sim :sim-state) :bool
  "Check if the receiver's data is a prefix of the sender's."
  (match-let* ((('sim-state ('sendstate ss &) ('recvstate rs &)) sim))
    (prefixp rs ss)))

(check= (prefixp '() '()) T)
(check= (prefixp '() '(1 2 3)) T)
(check= (prefixp '(1 2 3) '()) nil)
(check= (prefixp '(1 2 3 4) '(1 2 3)) nil)
(check= (prefixp '(1 4) '(1 2 3)) nil)
(check= (prefixp '(1 2) '(1 2 3)) T)

;; This lemma shows that given a list X that is smaller than and a
;; prefix of Y, adding the next element of Y maintains the prefix
;; property.
(defthm prefix-nth
  (implies (and
	    (tlp x)
	    (tlp y)
	    (prefixp x y)
	    (< (len x) (len y))
	    (== index (len x)))
	   (prefixp (app x (list (nth index y))) y)))

#| == The proof sketch ==

We know receiver state is a prefix of sender state (via C3), and that
the sender sequence number is equal to it's length (via C4). So we should
be able to utilize the prefix-nth lemma to show that the prefix property holds.
|#

;; This lemma shows that given a simulator state where the
;; receiver-sender prefix property holds, advancing the simulation by
;; one event will maintain this property.
(defthm simulator-step-prefix-property
  (implies (and (sim-statep sim)
		(rs-prefix-of-ssp sim)
		(eventp evt))
	   (rs-prefix-of-ssp (simulator-step sim evt)))
  ;; Applying the prefix-nth lemma to the OK and DROP-ACK subgoals
  :hints (("Subgoal 5'5'" :use (:instance prefix-nth
					  (y sim8)
					  (x sim9)
					  (index (len sim9))))
	  ("Subgoal 2'5'" :use (:instance prefix-nth
					  (y sim8)
					  (x sim9)
					  (index (len sim9))))))



;; Disabling the definition rule so we can use the lemma proved above
(in-theory (disable simulator-step-definition-rule))

;; This lemma shows that given a starting simulator state where the
;; receiver-sender prefix property holds, and any set of events to
;; occur during the simulation, the prefix property will hold after
;; applying the simulation to the starting conditions.
(defthm simulator-prefix-property
  (implies (and (sim-statep sim)
		(event-deckp evt)
		(rs-prefix-of-ssp sim))
	   (rs-prefix-of-ssp (simulator sim evt)))
  :hints (("Goal" :induct (simulator sim evt))))

;; QED.
