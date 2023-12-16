//Educator 
sig Educator {}

//A Permit is from one educator to a set of other educator, and regard only one tournament
sig Permit {
	tournamentCreator : one Educator,
	battleCreators : some Educator,
	tournament : one Tournament
}	{
	tournamentCreator not in battleCreators and
	tournament.creator = tournamentCreator and
	tournament.battleCreators = battleCreators
}

fact NoTwoPermissionAtSameEducator{
all disj p1, p2 : Permit | (p1.tournament = p2.tournament and p1.tournamentCreator = p2.tournamentCreator) implies (all bC : p1.battleCreators | bC not in p2.battleCreators)
}

//A tournament have a creator and a set of educator that can create battle
sig Tournament {
	creator : one Educator,
	battleCreators : set Educator
} 	{
}

//A battle have a creator and a tournament, the creator must be the creator or an educator that can create tournament
sig Battle {
	tournament : one Tournament,
	creator : one Educator,
	tests : set Test
}{
	creator in tournament.battleCreators or
	creator = tournament.creator
}

//Test of a battle
sig Test {}

//Student in CKB can have a set of badges
sig Student{
	badges : set Badge,
	tournament : set Tournament
}

//A repository is assigned to a group and is relative to one battle
sig Repository{
	group : one Group,
	battle : one Battle
}{
	group.battle = battle
}

fact onlyOneRepository {
	all disj r1, r2 : Repository | all g : r1.group | all b : r1.battle | b != r2.battle or g != r2.group 
}

//A group is formed by n student and partecipate to one tournament
sig Group{
	groupCreator : one Student,
	students : set Student,
	battle : lone Battle
}{
	groupCreator not in students	
}

fact noStudentsInMoreGroupInABattle{
	all s: Student | all disj g1, g2: Group | (s in g1.students and s in g2.students ) implies g1.battle != g2.battle 
}

//fact noEqualGroup{
//	all g1, g2:Group | g1!=g2
//}

//A badge is created by an educator
sig Badge{
	creator : one Educator,
	tournament : one Tournament
}{
	creator = tournament.creator
}

//An invite is made by a student of a group and direct to other student
sig Invite{
	sender : one Student,
	receiver : one Student,
	group : one Group
}{
	sender != receiver and
	sender = group.groupCreator 
}

fact SenderAndReceiverInSameTournament{
	all i : Invite | all r : i.receiver |  some t : r.tournament | t in i.sender.tournament
}

fact memberOfAGroupSameTournament{
	all g : Group | all disj s1, s2 : g.students | some t1 : s1.tournament | some t2 : s2.tournament | t1 = t2
}

fact StudentMustBeInAtLeastOneBattleInATournamentToReceiveBadges{
	all s:Student | all b : s.badges | all g: Group | s in g.students and g.battle.tournament = b.tournament
}

fact StudentsGroupBattleInTournament{
	all g : Group | all s : g.students | g.battle.tournament in s.tournament and g.battle.tournament in g.groupCreator.tournament
}

fact StudentInAGroup{
	all g : Group | all s : g.students | some i : Invite |
	i.sender = g.groupCreator and
	i.receiver = s  and 
	i.group = g
}


//TODO: Sistemare badges e tournament
pred show [] {
#Educator = 2
#Badge = 3
#Tournament = 3
#Student = 3
#Student.badges = 2
#Group.students = 1
#Repository = 2
#Group = 2
#Invite = 3
}

run show 





