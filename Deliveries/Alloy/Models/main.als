open b_signatures

/***************************************
	Signatures
****************************************/

//abstract class of user	
abstract sig User{
	notificationList: set Notification,
	email: one Email
}


sig Passenger extends User{
	bookingList: set Booking,
	releasedFeedback: set Feedback
}

sig TaxiDriver extends User{
	receivedFeedbacks: set Feedback,
	associatedZone: one Zone,
	carSeats: one Integer
}

sig Administrator extends User{
}

sig Booking{
	startingAddress: one Address,
	destinationAddress: one Address,
	estimatedRideDate: one Date,
	ride: one Ride,
	driver: lone TaxiDriver,
	passenger: one Passenger

}

sig Ride{
	associatedBooking: one Booking
}

sig Address{
	zone: one Zone
}

sig Zone{
	driverList: set TaxiDriver,
	addressList: set Address

}

sig Notification{
	notifiedUser: one User
}

sig Feedback{
	associatedRide: one Ride
}

/***************************************
	Facts
****************************************/

fact noDuplicateBooking{
	no disj b1,b2: Booking | (b1.startingAddress=b2.startingAddress) and (b1.destinationAddress=
	b2.destinationAddress) and (b1.passenger=b2.passenger) and (b1.estimatedRideDate=b2.estimatedRideDate)
	 }

fact noDuplicateUser{
	no disj u1,u2: User | (u1.email=u2.email)
}

fact userConsistence
{
	all u1, u2: User | u1.email = u2.email iff u1.notificationList = u2.notificationList
}
fact bookingConsistence
{
	//A booking is on the user's booking list iff he is the creator of that booking
	all p: Passenger, b: Booking | b in p.bookingList iff b.passenger = p
	//A Booking must have starting address and destination address different
	all b: Booking | b.startingAddress != b.destinationAddress
}
fact feedbackStructure
{
	all f:Feedback | some r:Ride | r = f.associatedRide
}
fact feedbackConsistence
{	
	//A feedback can be released iff the user has performed his ride
	all f:Feedback | some b: Booking | f.associatedRide = b.ride 
	//iff some r:Ride | r.associatedBooking = b
	//All feedbacks must have a releaser and a receiver that are associated to a booking in wich one is the passenger and one is the driver
}

fact carSeatsConstraint
{
	all t: TaxiDriver | #t.carSeats > 0 and #t.carSeats <= 6
}


/***************************************
	Predicates
****************************************/

pred show()
{
	#Passenger > 2
	#TaxiDriver>1
	#Feedback >1
	#Ride > 1
}
//Booking inserting in the list bookingLsit of Passenger (bookingList)
pred bookingInserting(b: Booking, bookingList : set Booking)
{
	b not in bookingList implies bookingList = bookingList + b
}

//Booking deleting
pred bookingDeleting(b: Booking, bookingList:set Booking)
{
	b in bookingList implies bookingList = bookingList - b
}

//Feedback inserting
pred feedbackReleasing(feedbackRecievedByTaxiDriver: set Feedback, r:Ride, b:Booking,  f:Feedback)
{
	f not in feedbackRecievedByTaxiDriver and b = r.associatedBooking implies feedbackRecievedByTaxiDriver = feedbackRecievedByTaxiDriver + f 
	
} 

/***************************************
	Runs
****************************************/
run show for 5

run bookingInserting for 2

run bookingDeleting for 2

run feedbackReleasing for 2

/***************************************
	Assertions
****************************************/

assert noBookingDuplication
{
	no disj b1, b2 : Booking  |  (b1.startingAddress=b2.startingAddress) and (b1.destinationAddress=
	b2.destinationAddress) and (b1.passenger=b2.passenger) and (b1.estimatedRideDate=b2.estimatedRideDate) 
}

check noBookingDuplication for 5

assert noUsersWithTheSameNotificationList
{
	no disj u1, u2: User | u1.notificationList = u2.notificationList
}

check noUsersWithTheSameNotificationList for 5

assert bookingCreation
{
	all b: Booking, p1: Passenger | (b not in p1.bookingList) and (bookingInserting[b,p1.bookingList]) implies  (b in p1.bookingList)
}
check bookingCreation for 5

assert bookingDeletion
{
	all b:Booking, p1: Passenger | (b in p1.bookingList) and (bookingDeleting[b, p1.bookingList]) implies (b not in p1.bookingList)
}
check bookingDeletion for 5

//There not exists a feedback for a specific booking that doesn't have assigned an existing ride
assert feedbackExistence
{
	all f:Feedback | one r:Ride | f.associatedRide = r
}
check feedbackExistence for 5
