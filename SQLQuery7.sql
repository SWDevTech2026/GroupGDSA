insert exam values(5, 'php', GETDATE()+7)

select * from exam
select * from examapp

-- cannot use insert in function(has to do calculation)
create function app(
				@examid int,
				@studentid int) returns int
as
begin
	declare @applied int, @limit int
begin tran

select @limit=limit from exam where id=@examid
select @applied=count(*) from examapp where examid=@examid

if(@applied<@limit)
begin
	insert into examapp
	values (@examid,@studentid)
	print 'Done!'
end
else
	begin
		print 'Exam is full!'
		return 1
	end
commit
	return 0
end

create function nr_app(
					@examid int) returns int
as
begin
	declare @results int
	select @results=count(*)
	from examapp
	where examid=@examid
return @results
end

select dbo.nr_app(1)


-- create function avail_exam(
alter function avail_exam(
						@dates datetime) returns table
as
return  
(select * from exam where @dates>dates)

select * from dbo.avail_exam(getdate()+1)


create function appl(
					@examid int) returns @app table
					(id int, 
					studentid int)
as
	begin
		insert into @app
		select id, studentid
		from exam e1 inner join examapp e2 on e1.id=e2.examid
		where e1.id=@examid
	return
	end

select * from dbo.appl(1)


-- question: how can we use select without table?
-- select function
select 5