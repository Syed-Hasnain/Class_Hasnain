#!/usr/bin/perl

# Added support for 4 array per pod setup - Shouvik
# Added support for vmax3 - Shouvik
# emcalloc.pl
# This is a new code base for emcalloc.pl
#       Features 1.0
#               + Complete re-write to work with strict and eliminate infinite loops
#               + Default input changed from prompt to cli options. Prompt available via -prompt flag
#               + Only requires one configuration file.  Kept -addfile and -initiatorfile for legacy support
#                       + all CLI options except the filename can be put into config file
#               + Code now runs based on EMC array type.
#                       + VMAX Support
#               + Added detailed loggig via -verbose option
#               + If a fatal error occurs, it cleans up any files it has already created
#               + Added ability to run SRDF configuration via -exec_srdf options
#                       + Will determine if we need to run cons_exempt procedure or not
#               + Added auto layout in configuration file.  See "Special Features" below
#               + Added WARNING if device is already mapped
#            1.1
#               + Added alias support for VMAX
#            1.1.1
#               + Added output of "Created" files for use with scriptrunner as CREATED_FILES
#           1.2
#               + Added support to toggle dynamic RDF flag for devices missing to it (ends up in convert file)
#               + Auto layout should now properly work for DMX4
#               + Added handeling of CTRL-C to cleanup files and write to log
#
# TO DO :
#       - Probably want to remove dependecy on maskings emcmask.pl easily replaceable with symmaskdb command (only used for dmx4).
#
#       - Replace safesymcli calls with DB CALLS (Search for DB CALL for subroutines that might benefit)
#
#### Config File Notes ####
# The configuration file will parse several lines in order to obtain it's information
#       Legacy Lines
#               WWN host hba fa:port    [ e.g. 2100000000000000 cs99-db1-1-sjl host5 3e:1 ]     This format requires 1 entry per hba / fa combination (formerly "initiatorfile")
#               fa:port DEV,DEV,DEV,... [ e.g. 3e:1 2000,6000,6050 ]                            This format requires 1 entry per FA (formerly "addfile")
#
#       Option Lines *NEW* -- These will overwrite CLI options to ensure repeatable results
#               asn <serial>            [ e.g. asn 4415 ]       Sets the serial number of the
#               sid <serial>            [ e.g. sid 4415 ]       Same as above, use either format
#               primary                                         Sets this site as the primary site
#               secondary                                       Sets this site as the secondary site
#               sfdc <case #>           [ e.g. sfdc 010008 ]    Sets the SFDC case #, default used if not specified
#               meta_width #            [ e.g. meta_width 4 ]   Specifies how wide each striped meta should be created.. Generally don't touch
#
#               rdf_dirs <dir,dir>              [ e.g. rdf_dirs 3d,4d,10d,13d ] Passes these RDF dirs as both local and remote dirs to the call to -exec_srdf
#               local_rdf_dirs <dir,dir>        [ e.g. rdf_dirs 8c,9c ] Passes these RDF dirs only for local side. MUST specify remote_rdf_dirs when using this option
#               remote_rdf_dirs <dir,dir>       [ e.g. rdf_dirs 8c,9c ] Passes these RDF dirs only for remote side. MUST specify local_rdf_dirs when using this option
#
#               name <name>             [ e.g. name cs99-db ]   Sets the logical name for this allocation
#                       Notes on "name", use the following for general allocation guidelines POD is like cs99
#                       WARNING : allocating everything all at once is generally not what you want to do
#                               - POD-db        -> DATADG and redo logs
#                               - POD-archive   -> ARCHDG
#                               - POD-noclone   -> voting/ocr, FLASHDG, oracle_home
#                               - POD-search    -> Search / Indexer allocations
#                               - POD-content   -> Content / csearch allocations
#
#       Operations Lines -- These tell us what functions you'd like to run
#               operations <function>,<function>...     [ e.g. operations meta,map ]    Specifies what operations we are to run
#
#               Operations functions:
#                       meta            Creates meta devices
#                       map             DMX - Maps devices to FA,  VMAX - creates auto provisioning groups
#                       alias           DMX - creates symmetrix aliases,  VMAX - creates auto provisioning groups
#                       mask            DMX - masks devices (Tries to use aliases, but if it can't figure them out it uses WWN),  VMAX - creates auto provisioning groups
#                       convert         Converts devices to the appropriate type e.g. 2-Way-Mir, BCV+TDEV etc...
#                       clone           Creates pairfile and begins cloning operations
#                       replication     Creates callback to this script to perform SRDF operations
#                       symdg           Creates the symdg groups and populates them
#                       doall           Do all of the above
#
#       Special functions :
#               WWN host HBA    -- When you leave off the FA port, you only need one entry per host, this is used in conjunction with dirs and devs options below
#                               -- It will take all of the devices and divide them up amongst FA pairs
#               dirs <fa:port,fa:port>  Specifies a group of ports to assign storage to, used with devs
#               devs <device,range,etc..> e.g. -devs 9000:90F0,A000 would assign all devices between 9000 -> 90F0 and device A000
#

use strict;
use warnings;
use Cwd 'abs_path';    ## Used only to find absolute path of this script, in order to perform srdf consistency exempt
use Getopt::Long;
use Data::Dumper;

##########################
## Required Global Vars ##
##########################
my %emcopts;         ## Stores Command line options
my %emcfg;           ## Stores configuration params
my %wwnnames;        ## Stores names like cs990-db1-1-chi_host5 => 200000000000000001
my %dgwwnnames;      ## Stores names for DG init file
my %host_mapping;    ## stores mappings recieved {host_hba}{fa:port} = 1
my %dghost_mapping;  ## stores mappings for DG init file
my %lun_mapping;     ## stores {fa:port}{DEVICE} = 1
my %fa_mapping;      ## Used for DMX4 mapping, holds a list of all devs down a given FA = {fa:port}{scsiID} = DEVICE;
my %device_info_list;## stores {DEVICE}{found}=1, needs to store devlist at the begining
my %device_info;     ## stores {ASN}{DEVICE}{found}=1, {ASN}{DEVICE}{meta}=no/head/member, {ASN}{DEVICE}{type}=2-Way-Mir, TDEV, etc....
my %rdf_info;        ## Stores RDF info {num} => name
my @devlist;         ## stores list of devices we are dealing with
my @clonelist;       ## stores list of clone devices we are dealing with
my @emc_logfile;     ## stores the emc_status output in a log array

## CLI Options. Name by itself indicates true, :s indicates string expected
my @emc_cli_options = (
    "help",              "verbose",    "prompt",          "force",
    "debug",             "asn:s",      "name:s",          "sfdc:s",
    "sid:s",             "session:s",  "primary",         "secondary",
    "file:s",            "addfile:s",  "initiatorfile:s", "meta_width:s",
    "doall",             "meta",       "map",             "convert",
    "mask",              "alias",      "clone",           "replication",
    "symdg",             "noclone",    "snapshot",        "noreplication",
    "exec_srdf",         "pairfile:s", "rdf_dirs:s",      "local_rdf_dirs:s",
    "remote_rdf_dirs:s", "p2s",        "format",          "dginitiatorfile:s",
    "3dc"
);

## This table handles label convernsions. Do not try to match the value back to the key, Spaces are important
my %device_type_labels = (
    '2-Way Mir'     => '2-Way-BCV-Mir',
    '2-Way BCV Mir' => '2-Way-Mir',
    'RAID-5'        => 'BCV+R-5',
    'BCV+R-5'       => 'RAID-5',
    'BCV+TDEV'      => 'TDEV',
    'RDF1+Mir'      => '2-Way-BCV+Mir',
    'TDEV'          => 'BCV+TDEV'
);
my %primary_device_types = ( '2-Way Mir' => '1', 'RAID-5' => '1', 'TDEV' => '1', 'RDF1+Mir' => '1' )
  ;    ## Valid device types STD @ primary / BCV @ secondary
my %secondary_device_types =
  ( '2-Way BCV Mir' => '1', 'BCV+R-5' => '1', 'BCV+TDEV' => '1' ); ## Valid device types BCV @ primary / STD @ secondary

## These two handle conversions for symdgs and rdf groups.. Based on name e.g. cs99-archive  would be cs99-arch-dgs (symdg) and cs99-arch (RDF)
my %convert_dg = (
    archive => 'arch-dgs',
    arch    => 'arch-dgs',
    db      => 'dgs',
    dgdb    => 'dgd',
    quorum  => 'NONE',
    noclone => 'NONE',
    flash   => 'NONE',
    search  => 'search-dgs',
    indexer => 'search-dgs',
    content => 'content-dgs',
    csearch => 'content-dgs'
);    ## Holds conversion info for SYMDG groups
my %convert_rdf = (
    archive => 'arch',
    arch    => 'arch',
    db      => 'dgs',
    quorum  => 'NONE',
    noclone => 'NONE',
    flash   => 'NONE',
    search  => 'srch',
    indexer => 'srch',
    csearch => 'cont',
    content => 'cont'
);    ## Holds conversion info for RDF groups

my %tmp_rdfgs = (
    66 => 'sync1-dgs',
    67 => 'sync2-dgs',
    68 => 'sync3-dgs',
    69 => 'sync4-dgs',
    76 => 'sync5-dgs',
    77 => 'sync6-dgs',
    78 => 'sync7-dgs',
    79 => 'sync8-dgs'
);    ## Hold temporary groups for cons-exempt procedure

my %default_rdf_ports = (
    'DMX'     => '3d,4d,7d,10d,13d,14d',
    'DMX4'    => '3d,4d,7d,10d,13d,14d',
    'VMAX'    => '3h,4h,7h,8h,9h,10h,13h,14h',
    'VMAX40K' => '3h,4h,7h,8h,9h,10h,13h,14h',
    'VMAX100K' => '1e:4,1e:24,3e:4,3e:24,2e:4,2e:24,4e:4,4e:24',
    'VMAX200K' => '1e:4,1e:24,3e:4,3e:24,2e:4,2e:24,4e:4,4e:24'
);    ## Holds default values for rdf ports

my %exec_srdf;    ## Holds SRDF commands

## Vmax Auto Provisioning hashes
my %exist_view;   ## Holds Existing view information Name => 1
my %exist_ig;     ## Holds Existing Initiator Group information IG => 1
my %exist_pg;     ## Holds Existing Port Group information PG => 1
my %exist_sg;     ## Holds Existing Storage Group information SG => 1

## Default hba pairing, for example host5 and host8 will always be given the same storage down different paths. Used only with special functions
my %hba_pairs = (
    host5 => 'host8',
    host7 => 'host6',
    host0 => 'host3',
    host2 => 'host1',
    c1    => 'c3',
    c5    => 'c7',
    c16   => 'c18'
);

###########################################
## User/Environment Specific Global Vars ##
###########################################
my $SYMCLI            = '/usr/symapi/bin'; ## Location for symcli binaries
my $DEFAULT_SFDC_CASE = 123456;            ## Default case ID if we don't specify. Set to 0 to force unique case number.

## Below used only to connect to remote syampi server
#$ENV{'SYMCLI_CONNECT'} = 'SYMAPIRBA';
#$ENV{'SYMCLI_CONNECT_TYPE'} = 'REMOTE';

#################
## Subroutines ##
#################
sub emc_usage {
    ## Prints usage for this script
    print <<EMC_USAGE_END;

usage $0
        -help           : this message
        -asn | -sid     : Array Serial Number
        -name           : name for allocation e.g. na9-db
        -prompt         : prompt for information instead of passing it
        -file           : Configuration file
        -addfile        : Add file (legacy)
        -initiatorfile  : Initiator file name (legacy)
        -dginitiatorfile: Initiator file name for dataguard array (required with -3dc option)
        -sfdc           : sfdc case number
        -primary        : Indicates this is an allocation at the primary datacenter
        -secondary      : Indicates this is an allocation at the secondary datacenter
        -meta_width     : Specifies width of meta devices (default is 16)
        -verbose        : prints warnings and non critical information
        -debug          : prints all messages, including debuging information
        -session        : manually sets a sessionid e.g. -session 444
        -force          : Allows for the allocation of luns already in use

        --- Operations ---
        -doall          : Performs all operations EXCEPT -exec_srdf
        -meta           : Creates 16way metas
        -convert        : Converts devices to the proper type
        -map            : Maps devices to front end ports
        -mask           : Masks devices to hba WWNS
        -alias          : Creates system aliases on DMX platform
        -clone          : Creates script to pair clones
        -replication    : Creates script to run SRDF replication
        -symdg          : Creates script to create and populate symdg

        -noclone        : Turns OFF cloning
        -noreplication  : Turns OFF replication, and symdg

        -3dc            : Four array pod allocation

        --- Below used to EXECUTE srdf procedure ---
        --- WARNING this procedure can take up to 3 days --
        -exec_srdf      : Indicates we wish to run the consistency exempt procedure
        -pairfile       : location of the pairfile
        -rdf_dirs       : Over-rides the default remote directors. e.g. 3h,4h,7h,10h
        -local_rdf_dirs : Used in conjunction with -remote_rdf_dirs when the RDF ports don't match on both sides
        -remote_rdf_dirs: Used in conjunction with -local_rdf_dirs when the RDF ports do not match on both sides
        -p2s            : Perform remote replication from pvol => svol (instead of default pvol => pvol)
        -format         : Use the latest format option when running createpair cmd, provided it meets all requirements


EMC_USAGE_END
}

sub check_root {
    ## Checks to see if we are run by root, if not it fails out.
    bailout ( 1, "Must be run with root permissions" ) unless ( $> == 0 );
}

sub get_user {
    ## Gets the username and uid of person running this if not root
    ## Input Hash reference, we will store the user_name and user_id in that hash
    my ($hashref) = @_;                 ## reference to hash caller wants us to use
    my $user      = getlogin ();
    my $uid       = getpwnam ($user);
    $hashref->{user_name} = $user;
    $hashref->{user_uid}  = $uid;
}

sub set_session_id {
    ## Sets session ID to the PID, can be used for logging or writing out files
    ## Input Hash reference, we will store the sessionid in that hash
    my ($hashref) = @_;

    ## If we passed an existing session in, we'll use it
    if ( defined $emcopts{session} ) { $hashref->{sessionid} = $emcopts{session}; }

    ## Otherwise we'll use use the PID
    else { $hashref->{sessionid} = $$; }
}

sub cleanup {
    ## Cleans up any files left over.  Called by bailout in the event of a failure
    ## These are the files we can cleanup
    my @files_created = (
        "metafile", "mapfile",   "aliasfile",       "convertfile", "maskfile", "clonefile",
        "pairfile", "symdgfile", "replicationfile", "autofile"
    );

    foreach (@files_created) {
        my $check_file = $_;

        ## Look for files we might have created in $emcfg and kill them
        if ( ( defined $emcfg{$check_file} ) && ( -e $emcfg{$check_file} ) ) {
            emc_status ( "CLEAN UP", "Removing $emcfg{$check_file}" );
            my @rmoutput = `rm $emcfg{$check_file}`;
        }
    }
}

sub list_scriptrunner {
    ## Spits out a list of "Action" files for constarnation to pass to scriptrunner.  Note that since no action is directly taken with pairfile we report on it
    my @file_list = (
        "convertfile",   "metafile",        "mapfile",     "autofile",     "maskfile",
        "clonefile",     "replicationfile", "symdgfile",   "aliasfile",
        "dgconvertfile", "dgautofile",      "dgaliasfile", "dgsymdgfile",
        "dgclonefile",   "dgreplicationfile"
    );
    my $created_files = 0;

    foreach (@file_list) {
        my $check_file = $_;

        ## Any file defined in $emcfg (that exists) we will report back
        if ( ( defined $emcfg{$check_file} ) && ( -e $emcfg{$check_file} ) ) {
            if   ($created_files) { $created_files = $created_files . "," . $emcfg{$check_file}; }
            else                  { $created_files = $emcfg{$check_file}; }
        }
    }

    if ($created_files) { emc_status ( "CREATED_FILES", $created_files ); }
}

sub stripit {
    ## Strips the leading and ending white space
    my ($stripstring) = @_;
    $stripstring =~ s/^\s+//;    ## Strips out leading white space
    $stripstring =~ s/\s+$//;    ## Strips out trailing white space
    return $stripstring;
}

sub fapartner {
    ## Get's an FA's partner using the rule of 17
    ## expected input is 3a:1 / 3A:1 / 3a1 / 3A1
    my ($thisfa) = @_;
    my ( $thisnum, $thisletter, $thisport, $partnernum );

    ## Matches 3a:1 format
    if ( $thisfa =~ /^(\d{1,2})([A-Ha-h]):([0-1])/ ) {
        $thisnum    = $1;
        $thisletter = $2;
        $thisport   = $3;
        $partnernum = 17 - $1;    ## applies rule of 17 to determine partner
        return "$partnernum" . "$thisletter" . ":$thisport";
    }

    ## Matches 3a1 format
    elsif ( $thisfa =~ /^(\d{1,2})([A-Ha-h])([0-1])/ ) {
        $thisnum    = $1;
        $thisletter = $2;
        $thisport   = $3;
        $partnernum = 17 - $1;    ## applies rule of 17 to determine partner
        return "$partnernum" . "$thisletter" . "$thisport";
    }

    bailout ( 10, "fapartner unable to determine partner for $thisfa, please ensure it's correct" )
      ;                           ## If we get here, it's not good
}

sub fapartner_r5 {
    ## Get's an FA's partner using the rule of 5 for vmax3
    ## expected input is 1d:1 / 1D:1 / 3d7 / 3D7
    my ($thisfa) = @_;
    my ( $thisnum, $thisletter, $thisport, $partnernum );

    ## Matches 1d:7, 1d:27 format
    if ( $thisfa =~ /^(\d{1})([DEde]):([0-9][0-9]{0,1})/ ) {
        $thisnum    = $1;
        $thisletter = $2;
        $thisport   = $3;
        $partnernum = 5 - $1;    ## applies rule of 5 to determine partner
        return "$partnernum" . "$thisletter" . ":$thisport";
    }

    ## Matches 1d7, 1d27 format
    elsif ( $thisfa =~ /^(\d{1})([DEde])([0-9][0-9]{0,1})/ ) {
        $thisnum    = $1;
        $thisletter = $2;
        $thisport   = $3;
        $partnernum = 5 - $1;    ## applies rule of 5 to determine partner
        return "$partnernum" . "$thisletter" . "$thisport";
    }

    bailout ( 10, "fapartner unable to determine partner for $thisfa, please ensure it's correct" )
      ;                           ## If we get here, it's not good
}

sub create_output_file {
    ## Input filename,UID,@file_lines
    ## We will write out filename with the contents of @lines, then change the owner to the UID passed
    ## called by any subroutine that writes a file
    my ( $filename, $uid, @lines ) = @_;
    my $filehandle;

    ## Make sure we got a valid filename and UID
    if ( ( !defined $filename ) || ( !defined $uid ) ) { bailout ( 10, "Uknown file ($filename) or UID ($uid)" ); }

    ## Make sure we can actually write the file
    if ( length ($filename) < 2 ) {
        bailout ( 40, "Output file name ($filename) too short, must be 2 or more characters" );
    }
    if ( -e $filename ) { bailout ( 41, "Unable to create output file ($filename), already exists" ); }
    emc_status ( "info", "writing file $filename" );

    ## Create The file, write the contents, then close it
    open $filehandle, ">", "$filename" or bailout ( 41, "Unable to create file ($filename) : $!" );
    foreach (@lines) { print $filehandle "$_\n"; }
    close ($filehandle);

    ## Set file permissions and change owner to uid passed in
    chmod ( 0744, $filename );
    chown ( $uid, -1, $filename );
}

sub safesymcli {
    ## called by many subs. This should only be used to call commands that query arrays
    ## First argument is ignore (0 or 1).. if 1 it will ignore errors
    ## Returns the output of the command run
    my ( $ignore, $mycmd ) = @_;
    my @myresults = ();    ## Results to return
    $mycmd = "$SYMCLI/" . $mycmd;
    emc_status ( "info", "safesymcli running ($mycmd)" );
    @myresults = `$mycmd 2>&1`;
    my $ecode = $? >> 8;
    if ( ( !$ignore ) && ($?) ) {

        foreach (@myresults) {    ## This will throw the error out to STDERR
            my $err = $_;
            chomp ($err);
            ## Only print non blank lines
            if ( !$err =~ /^$/ ) { emc_status ( "ERROR", $err ); }
        }
        bailout ( $ecode, "($mycmd) returned $ecode" );    ## exits and returns the same exit code as the failing cmd
    }
    return @myresults;
}

sub emc_create_logfile {
    ## Input filename,UID,@file_lines
    ## Writes the output file, basically same as create_output_file except we can't make calls to emc_status or bailout
    ## Any error in logfile creation will throw exit code 80
    ## called by emc_write_logfile
    my ( $filename, $uid, @lines ) = @_;
    my $filehandle;
    my $write_error = 0;

    ## Make sure we got a valid filename and UID
    if ( ( !defined $filename ) || ( !defined $uid ) ) {
        print "Error Unknown file ($filename) or UID ($uid)\n";
        exit 80;
    }

    ## Make sure we can actually write the file
    if ( length ($filename) < 2 ) {
        print "Output file name ($filename) too short, must be 2 or more characters\n";
        exit 80;
    }

    ## Create The file, write the contents, then close it
    open ( $filehandle, ">>", "$filename" ) or $write_error = $!;

    if ($write_error) {
        print "Unable to write logfile ($write_error), printing results!\n";
        for (@lines) { print "$_\n"; }
    }

    else {
        foreach (@lines) { print $filehandle "$_\n"; }
        close ($filehandle);

        ## Set file permissions and change owner to uid passed in
        chmod ( 0744, $filename ) or die "Unable to set permissions on logfile : $!";
        chown ( $uid, -1, $filename ) or die "Unable change owner on logfile : $!";
    }
}

sub emc_write_logfile {
    ## writes out the logfile, called by bailout , emc_exec_srdf_cmds, and end of script
    ## Format CASE_SESSIONID.log
    if ( @emc_logfile > 2 ) {
        my $thislogfile = "$emcfg{sfdc}" . "_$emcfg{sessionid}" . ".log";
        emc_create_logfile ( $thislogfile, $emcfg{user_uid}, @emc_logfile );
    }
}

sub bailout {
    ## Errors out script and returns error code
    ## If an error code of 1 is passed it will also display usage
    my ( $ecode, $ereason ) = @_;
    emc_status ( "ERROR", $ereason );
    if ( $ecode == 1 ) { emc_usage; }    ## Error code of 1 also spits out usage
    cleanup;                             ## Remove any temp files leftover
    emc_write_logfile;
    exit $ecode;
}

sub sig_bailout {
    bailout ( 99, "Interrupted by User" );
}

sub shortdate {
    ## Returns today in format of YYYYMMDD , used for output filenames
    my ( $sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst ) = localtime;
    $mon++;
    $year += 1900;
    my $returnline = sprintf ( "%04d%02d%02d", $year, $mon, $mday );
}

sub logtime {

    # Returns date for logging
    my ( $sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst ) = localtime;
    $mon++;
    $year += 1900;
    my $returnline = sprintf ( "[%02d/%02d/%04d %02d:%02d:%02d]", $mon, $mday, $year, $hour, $min, $sec );
    return $returnline;
}

sub emc_status {
    ## Prints the status messages to STDOUT or STDERR
    ## "info" and "warn" will only be showin in verbose, all others will be always shown
    my ( $lvl, $msg ) = @_;

    ## Save it to the logfile
    push ( @emc_logfile, logtime . " $lvl : $msg" );

    ## If the stats is ERROR we write it out to STDERR
    if ( $lvl eq "ERROR" ) { print STDERR "$lvl : $msg\n"; }
    elsif ( defined $emcopts{debug} ) { print logtime . " $lvl : $msg\n"; }
    elsif ( ( defined $emcopts{verbose} ) && ( $lvl ne "debug" ) ) { print logtime . " $lvl : $msg\n"; }
    elsif ( ( $lvl ne "info" ) && ( $lvl ne "warn" ) && ( $lvl ne "debug" ) ) { print logtime . " $lvl : $msg\n"; }
    ## No else needed, we just dont print anything
}

sub convert_yn {
    ## Converts y/n and true false into 0 or 1 for quicker use
    my ($convert_string) = @_;
    $convert_string = lc ($convert_string);    ## Making it lower case so we dont have to check for case
    my $return_num = 0;                        ## Retruns no/false as default
    if ( ( $convert_string eq "y" ) || ( $convert_string eq "true" ) ) { $return_num = 1; }
    return $return_num;
}

sub split_hex_range {
    ## Takes a hex range, splits it, and returns it as an array of individual devices
    ## you can adjust the first argument to count by 1 or 16 or any other number.
    my ( $myinc, $tmpdevrange ) = @_;
    my @devrange = split ( /,/, $tmpdevrange );
    my @returnlist = ();
    foreach (@devrange) {
        if (/:/) {
            my ( $mystart, $myend ) = split ( /:/, $_ );
            $mystart = hex ($mystart);
            $myend   = hex ($myend);
            for ( my $i = $mystart; $i <= $myend; $i = $i + $myinc ) {
                my $thishex = uc ( sprintf ( "%4x", $i ) );
                push ( @returnlist, "$thishex" );
            }
        }
        else { push ( @returnlist, "$_" ); }    ## Single device, push it and move on
    }
    return (@returnlist);
}

sub auto_map_luns {
    ## input $directors and $devs, both comma separated
    my ( $dirs, $devs ) = @_;
    my @device_list;
    my @dir_list;
    my %low_dirs;                               ## Temporarily stores lowest directors it finds
    my $dir_index = 0;                          ## counts unique dirs in order to index them
    my %dir_hash;
    my %round_robin;    ## Temporary hash we'll use to round robin devices across the lowest # director
    #workaround to get the array type as there is now a hardcoded VMAX3 entry for auto mapping to non rule-of-17 arrays
    my ( $fullsid, $arraytype, $enginuitycode ) = emc_get_array_info ( $emcopts{asn} );
    if ( ( $fullsid eq "NONE" ) || ( $arraytype eq "NONE" ) ) {
        bailout ( 10, "Unable to determine serial ($emcopts{asn}) or array type ($arraytype)" );
    }

    ## Get our devices split out into individual devices
    if   ( defined $emcopts{meta_width} ) { @device_list = split_hex_range ( $emcopts{meta_width}, $devs ); }
    else                                  { @device_list = split_hex_range ( 16,                   $devs ); }

    ## Split our directors up, we only want to keep the lowest one, so that we don't get duplicate entries
    my @rawdirs = split ( ',', $dirs );
    foreach (@rawdirs) {
        ## Lets make sure we're dealing with the same format of 3a1 or 3a:1
        if (/^(\d{1,2})([A-Ha-h]):*(0|1)/) {
            my $fa_num = $1;
            my $fa_let = lc ($2);
            my $fa_prt = $3;
            if ( $fa_num > 8 ) { $fa_num = 17 - $fa_num; }

            ## We only want ot store the lowest director in our hash .. 1-8,
            if ( !defined $low_dirs{ $fa_num . $fa_let . ":" . $fa_prt } ) {
                $low_dirs{ $fa_num . $fa_let . ":" . $fa_prt } = 1;    ##  Just holds it for fast checking later
                $dir_hash{$dir_index} = $fa_num . $fa_let . ":" . $fa_prt;
                $dir_index++;
            }
        }
    }
    my $cur_index = 0;
    foreach (@device_list) {
        if ( $cur_index <= $dir_index ) {
            push ( @{ $round_robin{$cur_index} }, $_ );
            $cur_index++;
            if ( $cur_index >= $dir_index ) { $cur_index = 0; }
        }
    }

    foreach my $index_key ( sort keys %round_robin ) {
        my $mydirs = 0;
        foreach ( @{ $round_robin{$index_key} } ) {
            my $thisdev = $_;
            my $thisfa  = $dir_hash{$index_key};
            my $partner;
            if ( $arraytype eq "VMAX100K" || $arraytype eq "VMAX200K" ) {
                 $partner = fapartner_r5 ($thisfa);
            } else {
                 $partner = fapartner ($thisfa);
            }
            ## Saves in lun_mapping as {fa:port}{device} = 1
            $lun_mapping{$thisfa}{$thisdev}    = 1;
            $lun_mapping{$partner}{$thisdev}   = 1;
            $device_info_list{$thisdev}{found} = 1;
        }
    }

    ## First we need to count our "hba" pairs
    my %unique_hbas;
    my $unique_count = 0;
    foreach my $key ( sort keys %wwnnames ) {
        my $thishba = $key;    ## e.g. cs99-db1-1-_hba5
        $thishba =~ s/^.*_//;  ## e.g. hba5
        ## we will store unique hbas = count... this lets us easily check them now with defined, then just reverse the hash to index them
        if ( ( defined $hba_pairs{$thishba} ) && ( !defined $unique_hbas{$thishba} ) ) {
            $unique_count++;
            $unique_hbas{$thishba} = $unique_count;
        }
    }

    ## Reverse unique hbas to make it an index
    my %runique_hbas = reverse %unique_hbas;
    my $count        = 1;                      # we'll use this count to round robin through the hba pairs
    foreach my $thisfa ( sort keys %low_dirs ) {
        if ( $count <= $unique_count ) {
            my $thishba       = $runique_hbas{$count};
            my $hbapartner    = $hba_pairs{$thishba};
            my $thisfapartner;
            if ( $arraytype eq "VMAX100K" || $arraytype eq "VMAX200K" ) {
                 $thisfapartner = fapartner_r5 ($thisfa);
            } else {
                 $thisfapartner = fapartner ($thisfa);
            }
            foreach my $hbakey ( keys %wwnnames ) {

                my $checkkey_partner = $hbakey;
                my $checkkey         = $hbakey;
                $checkkey_partner =~ s/_.*$//;    ## We just want the begining to add the partner hba later
                $checkkey         =~ s/^.*_//;    ## Should leave us with just "hba nane" so we can match em up

                if ( $checkkey eq $thishba ) {
                    $checkkey_partner = $checkkey_partner . "_" . $hba_pairs{$checkkey};
                    if ( !defined $host_mapping{$hbakey}{$thisfa} ) { $host_mapping{$hbakey}{$thisfa} = 1; }
                    if ( !defined $host_mapping{$checkkey_partner}{$thisfapartner} ) {
                        $host_mapping{$checkkey_partner}{$thisfapartner} = 1;
                    }
                }
            }
            $count++;
            if ( $count > $unique_count ) { $count = 1; }
        }
    }
}

sub emc_parse_config {
    ## Parses a config file for info (-file -initiatorfile -addfile)
    ## called by emc_get_config
    my $legacy_format = 0;    ## Tracks if we are using the manual legacy format
    my ($dgarray, @configlines) = @_; ## dgarray is boolean, 1 if it dgarray, 0 otherwise.
    my $dirs          = 0;    ## holds directors if we specify new format
    my $devs          = 0;    ## holds devices if we specify new format

    foreach (@configlines) {
        my $goodline = 0;

        if (/^\s*$/) { $goodline++; }    ## Blank lines are okay, and lines with only white space are ignored
        if (/^\s*#/) { $goodline++; }    ## Any line where the first non white char is a # is also good

        if (/^([0-9a-fA-F]{16})\s+(\S+)\s+(\S+)\s+(\S+)/) {
            ## matches e.g. 20000000000000001 cs99-db1-1-chi host5 3a:1
            $goodline++;
            $legacy_format++;
            my $thiswwn = lc ($1);
            my $thishba = lc ($2) . "_" . lc ($3);    ## format hostname_hbaname
            my $thisfa  = lc ($4);
            if ($dgarray) {
                if ( !defined $dgwwnnames{$thishba} ) { $dgwwnnames{$thishba} = $thiswwn; }
            } else {
                if ( !defined $wwnnames{$thishba} ) { $wwnnames{$thishba} = $thiswwn; }
            }
            if ($dgarray) {
                if ( !defined $dghost_mapping{$thishba}{$thisfa} ) { $dghost_mapping{$thishba}{$thisfa} = 1; }
            } else {
                if ( !defined $host_mapping{$thishba}{$thisfa} ) { $host_mapping{$thishba}{$thisfa} = 1; }
            }                                         ## Saves {host_hba}{fa:port} = 1;

            if ( !defined $emcfg{legacy_provisioning} ) { $emcfg{legacy_provisioning} = 1; }
        }
        elsif ( ( !$legacy_format ) && (/^([0-9a-fA-F]{16})\s*(\S*)\s*(\S*)/) ) {
            ## matches e.g. 20000000000000001 cs99-db1-1-chi host5
            $goodline++;
            my $thiswwn = lc ($1);
            my $thishba = lc ($2) . "_" . lc ($3);
            if ($dgarray) {
                if ( !defined $dgwwnnames{$thishba} ) { $dgwwnnames{$thishba} = $thiswwn; }
            } else {
                if ( !defined $wwnnames{$thishba} ) { $wwnnames{$thishba} = $thiswwn; }
            }

            if ( !defined $emcfg{auto_provisioning} ) { $emcfg{auto_provisioning} = 1; }
        }

        if ( (/^(\d{1,2}[A-Ha-h]:[0-1])[\s=]{1,3}([0-9A-Fa-f]{4}\S*)/) ||
           (/^(\d{1}d:[1-9][0-9]{0,1})[\s=]{1,3}([0-9A-Fa-f]{4}\S*)/) ){
            ## Added support for vmax 3, matches e.g. 1d:8 0000,AAAA and 1d:8=0000,0001
            ## matches e.g. 3a:1 0000,AAAA,etc...
            ## matches OR  3a:1=0000,AAAA,etc...
            $goodline++;
            $legacy_format++;
            my $thisfa    = lc ($1);    ## We only want lower case Fa's
            my $thesedevs = uc ($2);    ## we only want upper case device id's
            my (@thesedevs) =
              sort ( split ( /,/, $thesedevs ) );    ## Split all the comma separated devices out to a sorted array
            foreach (@thesedevs) {
                ## Run through each device and save it in lun_mappings as {fa:port}{DEVICE} = 1; this ensures we dont ever save things twice
                if ( !defined $lun_mapping{$thisfa}{$_} ) { $lun_mapping{$thisfa}{$_} = 1; }
                if ( !defined $device_info_list{$_}{found} ) { $device_info_list{$_}{found} =1;
                }                                    ## save the unique device in %device_info_list hash
            }
        }

        ## Get new formatted options devs and dirs in order to round robin them
        if ( ( !$legacy_format ) && (/^devs[\s=]{1,3}(\S*)/i) ) { $goodline++; $devs = $1; }
        if ( ( !$legacy_format ) && (/^dirs[\s=]{1,3}(\S*)/i) ) { $goodline++; $dirs = $1; }

        ## See if we are specifying our name
        if (/^name[\s:=]{1,3}(\S*)/i) { $goodline++; $emcopts{name} = lc ($1); }

        ## See if we are specifying our array
        if    (/^asn[\s:=]{1,3}(\S*)/i) { $goodline++; $emcopts{asn} = $1; }
        elsif (/^sid[\s:=]{1,3}(\S*)/i) { $goodline++; $emcopts{asn} = $1; }

        ## Check to see if we are primary DC
        if (/^primary/i) { $goodline++; $emcopts{primary} = 1; }

        ## Check to see if we are secondary DC
        if (/^secondary/i) { $goodline++; $emcopts{secondary} = 1; }

        ## Check to see if we are doing p2s replication
        if (/^p2s/i) { $goodline++; $emcopts{p2p} = 0; }

        ## Check to see if we are passing our case #
        if    (/^sfdc[\s:=]{1,3}(\d*)/i) { $goodline++; $emcopts{sfdc} = $1; }
        elsif (/^case[\s:=]{1,3}(\d*)/i) { $goodline++; $emcopts{sfdc} = $1; }

        ## Chceck for meta width
        if (/^meta_width[\s:=]{1,3}(\d{1,3})/i) { $goodline++; $emcopts{meta_width} = $1; }

        ## See if we are overwriting RDF directors
        if (/^rdf_dirs[\s:=]{1,3}(\S*)/i) { $goodline++; $emcfg{local_rdf_dirs} = $1; $emcfg{remote_rdf_dirs} = $1; }
        elsif (/^local_rdf_dirs[\s:=]{1,3}(\S*)/i)  { $goodline++; $emcfg{local_rdf_dirs}  = $1; }
        elsif (/^remote_rdf_dirs[\s:=]{1,3}(\S*)/i) { $goodline++; $emcfg{remote_rdf_dirs} = $1; }

        ## Lets look for Operations
        if (/^operations[\s:=]{1,3}(\S*)/i) {
            ## Matches "operations meta,map,doall,replication"
            $goodline++;
            my $myoperations = lc ($1);
            if ( $myoperations =~ /,/ ) {
                my (@myoperations) = split ( /,/, $myoperations );
                foreach (@myoperations) {
                    my $myopt = $_;
                    if ( !defined $emcopts{$myopt} ) { $goodline++; $emcopts{$myopt} = 1; }
                }
            }
            ## Or if we just have one operation
            else {
                if ( !defined $emcopts{$myoperations} ) { $emcopts{$myoperations} = 1; }
            }
        }

        ## We've done all of our checking for this line, lets make sure it's good
        if ( !$goodline ) { bailout ( 2, "Malformatted configuration line : $_" ); }
    }

    ## If we aren't doing the legacy format and if we found directors and devices then populate host_mapping, lun_mapping, and device_info
    if ( ( !$legacy_format ) && ($dirs) && ($devs) ) { auto_map_luns ( $dirs, $devs ); }
    else { emc_status ( "info", "legacy format detected, using manual mapping of storage to directors." ); }
}

sub get_config_lines {
    ## If a file exists we'll grab the lines and return them in an array
    ## Called by emc_get_config
    my ($thisfile) = @_;
    my @returnlines;    ## used to return the output
    unless ( -e $thisfile ) { bailout ( 100, "file $thisfile does not exist!!" ); }
    unless ( -r $thisfile ) { bailout ( 100, "file $thisfile is not readable!!" ); }
    open ( CONFIGFILE, $thisfile );
    my @rawconfiglines = <CONFIGFILE>;    ## Saves raw lines, we will parse out the junk in a second
    close (CONFIGFILE);

    foreach (@rawconfiglines) {
        if (/^[A-Za-z0-9]/) {
            ## Creating clean output that removes empty lines and lines with comments
            chomp ($_);
            push ( @returnlines, $_ );
        }
    }
    return @returnlines;
}

sub emc_get_config {
    ## Parses config file. If legacy -addfile or -initiatorfile are used, we concatonate those lines and throw them for parsing
    ## called by emc_main
    my @parselines;    ## Holds the contents of the config file to send off for parsing
    my $foundfile = 0; ## Tracks if we were passed any config file

    if ( defined $emcopts{addfile} ) {
        $foundfile++;
        my @addlines = get_config_lines ( $emcopts{addfile} );
        @parselines = ( @parselines, @addlines );
    }
    if ( defined $emcopts{initiatorfile} ) {
        $foundfile++;
        my @initlines = get_config_lines ( $emcopts{initiatorfile} );
        @parselines = ( @parselines, @initlines );
    }
    if ( defined $emcopts{file} ) {
        $foundfile++;
        my @filelines = get_config_lines ( $emcopts{file} );
        @parselines = ( @parselines, @filelines );
    }

    if ($foundfile) { emc_parse_config (0, @parselines); }    ## Parses all the files at once

    ## If we have a initfile for DG array then lets process it
    if ( defined $emcopts{dginitiatorfile} ) {
        my @initlines = get_config_lines ( $emcopts{dginitiatorfile} );
        emc_parse_config (1, @initlines);
    }
}

sub emc_prompt_opts {
    ## Gets the options via prompt instead of cli arguments
    ## Name = $emcopts{name} , Serial = $emcopts{asn}
    ## Gets Allocation name and stores it in emcopts{name}

    ## These are the values we will convert from y/n to 1/0
    my @truefalse = ( "primary", "meta", "doall", "symdg", "alias", "clone", "replication", "map" );

    ## Gathering the data from a prompt
    do { print "Allocation Name : "; chomp ( $emcopts{name} = <> ); }
      while ( !( defined $emcopts{name} ) || ( $emcopts{name} eq "" ) );
    do { print "Array Serial Number : "; chomp ( $emcopts{asn} = <> ); }
      while ( !( defined $emcopts{asn} ) || ( $emcopts{asn} eq "" ) );
    do { print "Valid Config File : "; chomp ( $emcopts{file} = <> ); }
      while ( !( defined $emcopts{file} ) || ( $emcopts{file} eq "" ) || !( -e $emcopts{file} ) );
    do { print "Primary Datacenter (y/n) : "; chomp ( $emcopts{primary} = lc (<>) ); }
      while ( !( defined $emcopts{primary} ) || ( ( $emcopts{primary} ne "n" ) && ( $emcopts{primary} ne "y" ) ) );

    ## Set primary or not
    if ( $emcopts{primary} eq "y" ) { $emcopts{primary} = 1; }
    elsif ( $emcopts{primary} eq "n" ) { $emcopts{secondary} = 1; undef $emcopts{primary}; }

    ## Should we just do everything?
    do {
        print "Perform All Operations (Metas, Mapping, Masking, Clones, Aliases, Replication, Symdg Creation) (y/n) : ";
        chomp ( $emcopts{doall} = lc (<>) );
    } while ( !( defined $emcopts{doall} ) || ( ( $emcopts{doall} ne "n" ) && ( $emcopts{doall} ne "y" ) ) );

    ## Not doing everything, lets ask one by one
    if ( $emcopts{doall} eq "n" ) {
        do { print "Create Meta Devices (y/n) : "; chomp ( $emcopts{meta} = lc (<>) ); }
          while ( !( defined $emcopts{meta} ) || ( ( $emcopts{meta} ne "n" ) && ( $emcopts{meta} ne "y" ) ) );
        do { print "Map Devices (y/n) : "; chomp ( $emcopts{map} = lc (<>) ); }
          while ( !( defined $emcopts{map} ) || ( ( $emcopts{map} ne "n" ) && ( $emcopts{map} ne "y" ) ) );
        do { print "Create Aliases (y/n) : "; chomp ( $emcopts{alias} = lc (<>) ); }
          while ( !( defined $emcopts{alias} ) || ( ( $emcopts{alias} ne "n" ) && ( $emcopts{alias} ne "y" ) ) );
        do { print "Create Clones (y/n) : "; chomp ( $emcopts{clone} = lc (<>) ); }
          while ( !( defined $emcopts{clone} ) || ( ( $emcopts{clone} ne "n" ) && ( $emcopts{clone} ne "y" ) ) );
        do {
            print "Create Replication (y/n) : ";
            chomp ( $emcopts{replication} = lc (<>) );
          } while ( !( defined $emcopts{replication} )
            || ( ( $emcopts{replication} ne "n" ) && ( $emcopts{replication} ne "y" ) ) );
        do { print "Create symdg group (y/n) : "; chomp ( $emcopts{symdg} = lc (<>) ); }
          while ( !( defined $emcopts{symdg} ) || ( ( $emcopts{symdg} ne "n" ) && ( $emcopts{symdg} ne "y" ) ) );
    }

    ## Change y/n response into a 0/1 response for faster checking later
    foreach (@truefalse) {
        if ( defined $emcopts{$_} ) { $emcopts{$_} = convert_yn ( $emcopts{$_} ); }
    }
}

sub emc_check_noclone {
    ## Any symdg or symrdf group set to none will have cloning,replication and symdg disabled
    ## by referencing the name against %convert_dg and %convert_rdf looking for "NONE"

    ## Break our name down first
    my $basename = $emcopts{name};    ## Holds what we are allocating e.g. cs99
    my $nametype = $emcopts{name};    ## Holds the type of allocation e.g. archive
    $basename =~ s/-.*$//;            ## Chops off the dash and everything after it
    $nametype =~ s/^.*-//;            ## Chops off the dash and everything before it

    ## If we find the name in %convert_dg and it's NONE we're going to turn off clone and replication
    if ( defined $convert_dg{$nametype} ) {
        if ( $convert_dg{$nametype} eq "NONE" ) {
            if ( defined $emcopts{clone} )       { undef $emcopts{clone}; }
            if ( defined $emcopts{replication} ) { undef $emcopts{replication}; }
            if ( defined $emcopts{symdg} )       { undef $emcopts{symdg}; }
        }
    }

    ## If we find the name in %convert_rdf and it's NONE we're going to turn off clone and replication
    if ( defined $convert_rdf{$nametype} ) {
        if ( $convert_rdf{$nametype} eq "NONE" ) {
            if ( defined $emcopts{clone} )       { undef $emcopts{clone}; }
            if ( defined $emcopts{replication} ) { undef $emcopts{replication}; }
            if ( defined $emcopts{symdg} )       { undef $emcopts{symdg}; }
        }
    }

    ## If we specify noclone from the command line then we'll turn it off as well
    if ( ( defined $emcopts{noclone} ) || ( defined $emcopts{snapshot} ) ) {
        emc_status ( "info", "called with -noclone or -snapshot option, turning off clones" );
        if ( defined $emcopts{clone} ) { undef $emcopts{clone}; }
    }

    ## Same for noreplication
    if ( defined $emcopts{noreplication} ) {
        emc_status ( "info", "called with -noreplication option, turning off replication and symdg" );
        if ( defined $emcopts{replication} ) { undef $emcopts{replication}; }
        if ( defined $emcopts{symdg} )       { undef $emcopts{symdg}; }
    }

}

sub emc_parse_opts {
    ## Collects options into %opts hash and makes sure we have everything we expect
    # Prints usage if we pass no arguments, if we get bad arguments, or if we do -help
    my @arg_copy = @ARGV;    ## Holds a copy of our CLI options

    ## Gets CLI Options and stores them in %emcopts. If you want to add new options add to @emc_cli_options at the top
    emc_usage && exit 0
      if ( ( @ARGV < 1 ) || ( !GetOptions ( \%emcopts, @emc_cli_options ) ) || ( defined $emcopts{help} ) );

    if ( defined $emcopts{prompt} ) { emc_prompt_opts; }    ## If -prompt passed lets go get the options the long way

    ## For 4 array allocation we need initiator file for DG node
    if ( ( $emcopts{'3dc'} )  && ( ! defined $emcopts{exec_srdf} ) ) {
        if (! $emcopts{dginitiatorfile} ) { bailout ( 1, "Must provide dginitiator file when using -3dc option." ); }
    }
    ## By defualt we turn on p2p, unless p2s is specified
    if ( $emcopts{p2s} ) {
        $emcopts{p2p} = 0;
        if ( $emcopts{'3dc'} ) { bailout ( 1, "3dc allocation is NOT designed to work with p2s, only p2p." ); }
    } else {
        $emcopts{p2p} = 1;
    }


    ## If a file was specified we'll parse that before looking for missing info
    emc_get_config;

    ## Verify we have some basic information
    if ( ( !defined $emcopts{asn} ) && ( defined $emcopts{sid} ) ) { $emcopts{asn} = $emcopts{sid}; }
    elsif ( !defined $emcopts{asn} ) { bailout ( 1, "Must specify array serial." ); }    ## Need a Serial #
    if ( ( !defined $emcopts{sfdc} ) && ( $DEFAULT_SFDC_CASE == 0 ) ) {
        bailout ( 1, "SFDC Case # Required" );
    }                                                                                    ## Enforcing unique cases?
    if ( !defined $emcopts{sfdc} ) {
        $emcopts{sfdc} = $DEFAULT_SFDC_CASE;
    }    ## Sets generic case number if we didn't find one
    $emcfg{sfdc} = $emcopts{sfdc};    ## Saves case number in our config array for later reference
    if ( !defined $emcopts{name} ) { bailout ( 1, "Must specify name for allocation." );    ## Need a name e.g. cs99-db
                                } else {
                                        my ( $podName, $podType ) = split ( /-/, $emcopts{name} );
                                        if (lc($podType) eq "archive") { $podType = "arch";}
                                        if (lc($podType) eq "dataguard") { $podType = "dgdb";}
                                        $emcopts{name}   = $podName . "-" . $podType;
                                        $emcopts{dgname} = $podName . "-dgdb";
                                }
    if ( ( !defined $emcopts{primary} ) && ( !defined $emcopts{secondary} ) ) {
        bailout ( 1, "Must specify -primary OR -secondary." );
    }    ## need either primary or secondary
    if ( ( defined $emcopts{primary} ) && ( defined $emcopts{secondary} ) ) {
        bailout ( 1, "Must specify only -primary OR -secondary." );
    }    ## don't want both primary and secondary
    if   ( defined $emcopts{primary} )   { $emcfg{primary} = 1; }    ## Save $emcfg{primary} as true
    if   ( defined $emcopts{secondary} ) { $emcfg{primary} = 0; }    ## Save $emcfg{primary} as false

    ## See if we are overwriting RDF directors
    if (   ( defined $emcopts{rdf_dirs} )
        && ( ( defined $emcopts{local_rdf_dirs} ) || ( defined $emcopts{remote_rdf_dirs} ) ) )
    {
        bailout ( 1, "Do not specify -rdf_dirs in conjunction with -local_rdf_dirs or -remote_rdf_dirs" );
    }
    elsif ( defined $emcopts{rdf_dirs} ) {
        $emcfg{local_rdf_dirs}  = $emcopts{rdf_dirs};
        $emcfg{remote_rdf_dirs} = $emcopts{rdf_dirs};
    }
    if ( defined $emcopts{local_rdf_dirs} )  { $emcfg{local_rdf_dirs}  = $emcopts{local_rdf_dirs}; }
    if ( defined $emcopts{remote_rdf_dirs} ) { $emcfg{remote_rdf_dirs} = $emcopts{remote_rdf_dirs}; }
    if ( ( defined $emcfg{local_rdf_dirs} ) && ( !defined $emcfg{remote_rdf_dirs} ) ) {
        bailout ( 1, "local_rdf_dirs specified but remote_rdf_dirs is not" );
    }
    if ( ( !defined $emcfg{local_rdf_dirs} ) && ( defined $emcfg{remote_rdf_dirs} ) ) {
        bailout ( 1, "remote_rdf_dirs specified but local_rdf_dirs is not" );
    }

    ## IF we are doing everything set all the options to true now so we dont have to worry about it later
    ## NOTE: If you add true/false @emc_cli_options that you want to be part of doall they need to be set here
    if ( defined $emcopts{doall} ) {
        $emcopts{meta}        = 1;
        $emcopts{map}         = 1;
        $emcopts{clone}       = 1;
        $emcopts{alias}       = 1;
        $emcopts{replication} = 1;
        $emcopts{mask}        = 1;
        $emcopts{convert}     = 1;
        $emcopts{symdg}       = 1;
    }

    ## Turn off clone option if it is 4 array setup
    if   ( $emcopts{'3dc'} ) { undef $emcopts{clone}; }
    ## If we are using -force option, that means devs are in mapped state, hence we cannot use -format to create pair
    if ( defined $emcopts{force} ) {
        undef($emcopts{format});
    }

    if   ( !defined $emcopts{clone} )    { $emcfg{clone}   = 0; }    ## didn't specify clones, so we'll assume false
    else                                 { $emcfg{clone}   = 1; }    ## We want clones, setting $emcfg{clone} to true

    ## Lets make sure we are doing something
    if (   ( !defined $emcopts{meta} )
        && ( !defined $emcopts{map} )
        && ( !defined $emcopts{clone} )
        && ( !defined $emcopts{alias} )
        && ( !defined $emcopts{replication} )
        && ( !defined $emcopts{mask} )
        && ( !defined $emcopts{convert} )
        && ( !defined $emcopts{symdg} )
        && ( !defined $emcopts{exec_srdf} ) )
    {
        bailout ( 1, "no actions specified" );
    }

    ## Check if our name is special and requires no clones or no replication
    emc_check_noclone;

    ## We only want to pull detailed device info if we have to, so checking for some conditions
    ## Pulling device detail is very expensive with symdev.. DB CALLS make make this check obsoete
    if (   ( defined $emcopts{convert} )
        || ( defined $emcopts{meta} )
        || ( defined $emcopts{clone} )
        || ( defined $emcopts{replication} )
        || ( defined $emcopts{mask} ) )
    {
        $emcfg{need_dev_detail} = 1;
    }
    else { $emcfg{need_dev_detail} = 0; }

    emc_status ( "info", "script called $0 @arg_copy" );
}

sub emc_get_array_info {
    ## Gets the array type and sid for any serial matching $checksid
    ## called by emc_set_array_info
    ## returns NONE if invalid serial
    ## SHOULD BE REPLACED WITH DB CALLS WHEN DB IS LIVE
    my ($checksid) = @_;
    my $returnsid  = "NONE";
    my $returntype = "NONE";
    my $returncode = "NONE";
    my @results = safesymcli ( 0, "symcfg list" );
    foreach (@results) {
        if (/^\s*(\d{12})\s*(\w*)\s*(\w*)([\-|\d|\w]{0,3})\s*(\d{4})/) {
            my $thisserial = $1;
            my $thislocale = $2;
            my $thistype   = $3;
            my $thiscode   = $5;
            if ( $thisserial =~ m/$checksid$/ ) {
                ## Found a partial match of the serial
                if ( $returnsid ne "NONE" ) {
                    bailout ( 10, "Array serial not specific enough." );
                }    ## We have already found a valid SID, so this wasn't specific enough
                $returnsid  = $thisserial;
                $returntype = $thistype;
                $returncode = $thiscode;
            }
        }
    }
    return ( $returnsid, $returntype, $returncode );
}

sub emc_set_array_info {
    ## Called by emc_main
    ## Verfies array serial number and array type
    ## Stores full sid in $emcfg{sid} and $emcfg{array_type}
    my ( $fullsid, $arraytype, $enginuitycode ) = emc_get_array_info ( $emcopts{asn} );
    if ( ( $fullsid eq "NONE" ) || ( $arraytype eq "NONE" ) ) {
        bailout ( 10, "Unable to determine serial ($emcopts{asn}) or array type ($arraytype)" );
    }
    $emcfg{sid}        = $fullsid;
    $emcfg{array_type} = $arraytype;
    $emcfg{ecode_vers} = $enginuitycode;

    ## If our allocation type is 3dc, then we need to find out local partner array details
    if ( $emcopts{'3dc'} ) {
         emc_status ( "INFO", "3dc allocation detected, determining local DG array details." );
         emc_get_rdfinfo_vmax3('local');
         ( $fullsid, $arraytype, $enginuitycode ) = emc_get_array_info ( $emcfg{array_pair} );
         emc_status ( "INFO", "Local partner array: $fullsid." );
         $emcfg{partner_sid}        = $fullsid;
         $emcfg{partner_array_type} = $arraytype;
         $emcfg{parter_ecode_vers}  = $enginuitycode;
         undef $emcfg{array_pair};
    }

    ## Lets see what type of provisioning we are doing and report on it
    if ( defined $emcfg{auto_provisioning} ) {
        emc_status ( "info", "Auto provisioning detected. Automatically laying out luns." );
    }
    elsif ( defined $emcfg{legacy_provisioning} ) {
        emc_status ( "info", "Legacy provisioning detected. Using config file layout." );
    }
}

sub emc_set_symdg_name {
    ## Sets our symdg name as $emcfg{symdg}

    ## Only bothering if we haven't already determined our name
    if ( !defined $emcfg{symdg} ) {

        ## If we can't determine our name, then bailout
        if ( !defined $emcopts{name} ) { bailout ( 10, "Unable to determine my name, can't create symdg group" ); }

        ## Chop our name down into a basename and a nametype
        my $basename = $emcopts{name};    ## Holds what we are allocating e.g. cs99
        my $nametype = $emcopts{name};    ## Holds the type of allocation e.g. archive
        $basename =~ s/-.*$//;            ## Chops off the dash and everything after it
        $nametype =~ s/^.*-//;            ## Chops off the dash and everything before it

        ## convert the name if the nametype exists in %convert_dg
        if ( defined $convert_dg{$nametype} ) {
            if   ( $convert_dg{$nametype} ne "NONE" ) { $emcfg{symdg} = "$basename-" . $convert_dg{$nametype}; }
            else                                      { $emcfg{symdg} = "NONE"; }
        }

        ## If we couldn't figure it out we'll just use the name passed
        if ( !defined $emcfg{symdg} ) { $emcfg{symdg} = $emcopts{name}; }
    }
    if ( $emcopts{'3dc'} && !defined $emcfg{symdgDG} ) {
        ## If we can't determine our DG name, then bailout
        if ( !defined $emcopts{dgname} ) { bailout ( 10, "Unable to determine DG name, can't create symdg group" ); }
        ## Chop our name down into a basename and a nametype
        my $basename = $emcopts{dgname};    ## Holds what we are allocating e.g. cs99
        my $nametype = $emcopts{dgname};    ## Holds the type of allocation e.g. archive
        $basename =~ s/-.*$//;            ## Chops off the dash and everything after it
        $nametype =~ s/^.*-//;            ## Chops off the dash and everything before it

        ## convert the name if the nametype exists in %convert_dg
        if ( defined $convert_dg{$nametype} ) {
            if   ( $convert_dg{$nametype} ne "NONE" ) { $emcfg{symdgDG} = "$basename-" . $convert_dg{$nametype}; }
            else                                      { $emcfg{symdgDG} = "NONE"; }
        }

        ## If we couldn't figure it out we'll just use the name passed
        if ( !defined $emcfg{symdgDG} ) { $emcfg{symdgDG} = $emcopts{dgname}; }

    }
}

sub emc_set_rdfg_name {
    ## Sets our RDF name as $emcfg{symrdfg}

    ## Only bothering if we haven't already determined our name
    if ( !defined $emcfg{symrdfg} ) {

        ## If we can't determine our name, then bailout
        if ( !defined $emcopts{name} ) { bailout ( 10, "Unable to determine my name, can't create rdf group" ); }

        ## Chop our name down into a basename and a nametype
        my $basename = $emcopts{name};    ## Holds what we are allocating e.g. cs99
        my $nametype = $emcopts{name};    ## Holds the type of allocation e.g. archive
        $basename =~ s/-.*$//;            ## Chops off the dash and everything after it
        $nametype =~ s/^.*-//;            ## Chops off the dash and everything before it

        ## convert the name if the nametype exists in %convert_rdf
        if ( defined $convert_rdf{$nametype} ) {
            if   ( $convert_rdf{$nametype} ne "NONE" ) { $emcfg{symrdfg} = "$basename-" . $convert_rdf{$nametype}; }
            else                                       { $emcfg{symrdfg} = "NONE"; }
        }

        ## If we couldn't figure it out we'll just use the name passed
        if ( ( !defined $emcfg{symrdfg} ) && ( length ( $emcopts{name} ) < 11 ) ) { $emcfg{symrdfg} = $emcopts{name}; }

        ## SRDF names must be 10 chars or less, if we couldnt figure one out we'll need to bail out
        elsif ( !defined $emcfg{symrdfg} ) { bailout ( 50, "Unable to create rdf name, $emcopts{name} too long" ); }
    }
}

sub emc_fa_used {
    ## Determines FA ports SCSIID usage and stores them in a hash
    ## called by emc_run_dmx_map
    ## symcfg call SHOULD BE REPLACED BY DB CALL when available
    foreach my $key ( sort keys %lun_mapping ) {
        ## key is fa:port
        my $thisfa   = $key;
        my $thisport = $key;
        $thisfa   =~ s/:[0-1]//;               ## strip out :port
        $thisport =~ s/^[0-9]{1,2}[a-h]://;    ## Strip out FA:
        my @output = safesymcli ( 1, "symcfg -sid $emcfg{sid} list -dir $thisfa -p $thisport -address" );
        foreach (@output) {
            ## Run through the lines looking for used ports
            if (/^No devices are mapped to the specified port/) {
                emc_status ( "info", "No devices mapped to $thisfa" . ":$thisport" );
            }
            if (/^.{27}([0-9A-Fa-f]{4}).{42}([0-9A-Fa-f]{3})/) {
                ## matches DEVICE SCSIID
                ## We found a line containing DEVICE - FA slot... we are going to mark this slot as used for both this FA and it's partner
                ## This ensures we map to the same scsi id when we lookup free ports
                my $thisdev = $1;
                my $thismap = $2;                  ## this is in hex, be careful
                my $partner = fapartner ($key);    ## Find our partner FA
                if ( !defined $fa_mapping{$key}{$thismap} ) { $fa_mapping{$key}{$thismap} = $thisdev; }
                if ( !defined $fa_mapping{ fapartner ($key) }{$thismap} ) {
                    $fa_mapping{$partner}{$thismap} = $thisdev;
                }
            }
        }
    }
}

sub rough_hex_ranges {
    ## look through the device_info array for our devices, then put them into rough hex ranges
    ## if a device is more than 16 devices off of the previous one, we'll assume it's a new hex range
    ## If we don't find more than one device in a range we'll just push the single device
    ## Return array of RANGES   e.g. 0000:000A,1000:10010,8000:80FF, etc....
    my @rawdevlist = @_;

    my @roughranges = ();    ## Array to return with list of ranges
    my $thisdev;             ## Holds current device we are looking at
    my $foundstart  = 0;     ## Indicates we've found the start of our first range
    my $thisrange   = "";    ## First device in any given range
    my $lastinrange = "";    ## Last device found in the range so far
    my $defined_range = 15;  ## Hex Range for old arrays we have 16way meta, not for vmax3

    if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) { $defined_range = 0; }

    foreach (@rawdevlist) {
        $thisdev = $_;
        if ( !$foundstart ) {
            ## Start of our first range
            $foundstart++;    ## We found the start, set it to true
            $thisrange = $thisdev;
            emc_status ( "debug", "rough_hex_ranges setting range start to $thisrange" );
            $lastinrange = sprintf ( "%04X", hex ($thisdev) + $defined_range );
            emc_status ( "debug", "rough_hex_ranges setting lastinrange to $lastinrange" );
        }
        elsif ( hex ($thisdev) <= ( hex ($lastinrange) + $defined_range + 1 ) ) {
            ## This device is within 16 of the last devices we found in this range
            $lastinrange = sprintf ( "%04X", hex ($thisdev) + $defined_range );
            emc_status ( "debug", "rough_hex_ranges setting lastinrange to $lastinrange" );
        }
        else {
            ## This is not part of the last range, lets push it
            if ( $thisrange eq $lastinrange ) {
                push ( @roughranges, "$thisrange" );
            }    ## Only one device in last range, so just push it
            else { push ( @roughranges, "$thisrange:$lastinrange" ); }    ## Push the entire range

            ## Reset our our tracking vars
            $thisrange   = $thisdev;                                      ## Start a new range
            $lastinrange = $thisdev;
        }
    }

    ## Need to push the last range we found
    if ( $thisrange eq $lastinrange ) {
        push ( @roughranges, "$thisrange" );
    }    ## Only one device in last range, so just push it
    else { push ( @roughranges, "$thisrange:$lastinrange" ); }    ## Push the entire range

    return @roughranges;
}

sub emc_get_next_fa_avail {
    ## Input is fa:port
    ## Returns next available lun using %fa_mapping
    ## called by emc_run_dmx_map
    my ($fa) = @_;
    ## Loop 0 through 4096 , then conver to hex to see if scsi id is in use
    for ( my $scsidec = 0; $scsidec <= 4096; $scsidec++ ) {
        my $scsihex = uc ( sprintf ( "%03X", $scsidec ) );
        if ( !defined $fa_mapping{$fa}{$scsihex} ) {
            return $scsihex;
        }    ## if this scsi id doesn't exist for an FA return it
    }
    bailout ( 30, "Unable to determine next available ID for FA-$fa" );    ## None found, let's bail
}

sub symconfigure_human_header {
    ## Creates the human header  for symconfigure output files
    ## Input is current filename, output is array of output lines
    my ($filename) = @_;
    my @returnlines = ();

    push ( @returnlines, "## Execute the following commands against this file.  Ensure no errors at each step." );
    push ( @returnlines, "## $SYMCLI/symconfigure -sid $emcfg{sid} -f $filename preview" );
    push ( @returnlines, "## $SYMCLI/symconfigure -sid $emcfg{sid} -f $filename commit" );
    push ( @returnlines, "##" );
    push ( @returnlines, "## " . logtime . " Created automatically by $0 @ARGV" );
    push ( @returnlines, "##" );

    return @returnlines;
}

sub emc_parse_symdev {
    ## Parses symdev show output and stores the info
    ## Only parses one device worth at a time.  If you want to pass multiple devices, sort it out before passing
    ## SUB SHOULD BE REMOVED/REPLACED WITH DB CALLS WHEN DB IS LIVE
    ## called by emc_verify_devices
    my ($arraysid, @mylines) = @_;
    my ( $device_name, $device_type );
    my $meta_type       = "NONE";    ## Default meta type is none
    my $warned          = 0;         ## Lets us know if we've warned on this device already, dont want to spam
    my $dyn_rdf_enabled = 1;

    foreach (@mylines) {
        if (/^\s*Device Symmetrix Name\s*:\s([0-9A-Fa-f]{4,5})/) { $device_name = substr($1, -4); }
        if (/^\s*Device Configuration\s*:\s(.*)\s\s/) {
            $device_type = stripit ($1);
        }                            ## Pulls the device configuration e.g. 2-Way-Mir, TDEV
        if (/^\s*Device Configuration\s*:\s.*Meta\s(\w*)/) { $meta_type = $1; }    ## If a meta, matches the Head/Member

        ## See if this device is mapped already, if so , just throw a warning
        if ( (/^\s{4}Front Director Paths \((\d*)\)/) && ( !$warned ) ) {
            my $mapped_ports = $1;
            $warned++;
            if ( ( $mapped_ports > 0 ) && ( $meta_type ne "Member" ) && ( defined $emcopts{force} ) ) {
                emc_status ( "WARNING", "Array $arraysid: $device_name already mapped to \($mapped_ports\) ports" );
            }
            elsif ( ( $mapped_ports > 0 ) && ( $meta_type ne "Member" ) ) {
                bailout ( 99,
                    "WARNING Array $arraysid: $device_name already mapped to \($mapped_ports\) ports. Use -force to override." );
            }
        }

        ## See if dynamic RDF is turned off
        if (/^\s+Dynamic RDF Capability\s+:\s+None/) { $dyn_rdf_enabled = 0; }

    }

    ## Lets store info about devices we want to deal with
    $device_info{$arraysid}{$device_name}{device_type} = $device_type;    ## Stores our device_type;
    $device_info{$arraysid}{$device_name}{meta_type}   = $meta_type;      ## Member / Head / NONE
    if ( !$dyn_rdf_enabled ) { $device_info{$arraysid}{$device_name}{dynamic_rdf} = "no"; }
}

sub emc_verify_devices {
    ## Gathers device information. Takes symdev output and passes it along for parsing
    ## SYMDEV CODE SHOULD BE REPLACED WITH DB CALLS WHEN DB IS LIVE
    my ($arraysid, @checkdevs) = @_;                                      ## Devices we want to verify
    my @symdevout = ();

    ## If we are doing clones we need to check them out
    if ( $emcopts{clone} ) {
        my @clonedevs = emc_get_clones (@checkdevs);    ## Saves my clones
        foreach (@clonedevs) {
            if ( !defined $device_info{$arraysid}{$_}{found} ) { $device_info{$arraysid}{$_}{found} = 1; }
        }                                                        ## We need to flag these as interesting devices
        @checkdevs = sort ( @checkdevs, @clonedevs );    ## Combines the standards and the clones for investgiation
    }

    my @devranges = rough_hex_ranges (@checkdevs);       ## Combines our devices into rough ranges

    foreach (@devranges) {
        ## Parse each range at a time, should be quicker than pulling entire array
        my $firstdevice = 1;                             ## Tells loop if we're still on the first device
        my @thisdevice  = ();                            ## holds lines for single device parsing

        if (/:/) {
            @symdevout = safesymcli ( 0, "symdev -sid $arraysid list -RANGE $_ -v" );
        }                                                ## Looking at an entire range
        else { @symdevout = safesymcli ( 0, "symdev -sid $arraysid show $_" ); }    ## Looking at single device

        ## Run through each range and parse out th edevice info
        foreach (@symdevout) {
            if (/^\s*Device Physical Name/) {
                ## First line of a new device
                if ( !$firstdevice ) {
                    ## New Device, but not first one
                    emc_parse_symdev ($arraysid, @thisdevice);  ## Throw last device for parsing
                    undef (@thisdevice);                        ## Clear array to use again
                }
                else { $firstdevice = 0; }                      ## First device, clear flag
                push ( @thisdevice, $_ );                       ## Push this line either way
            }
            else { push ( @thisdevice, $_ ); }     ## Non header, push for next go-around
        }
        emc_parse_symdev ($arraysid, @thisdevice); ## Parse the last device we found in the range
        undef (@thisdevice);
    }
}

sub emc_get_clones {
    ## Input @array_of_devices    Output: @array_of_clones
    ## Converts devices to clones
    my (@srcdevs) = @_;
    my @returndevs = ();
    my ( $thisdev, $firstchar, $otherchars );

    foreach (@srcdevs) {
        $thisdev = $_;
        if (/^([0-9A-F])([0-9A-Fa-f]{3})/) {
            $firstchar  = $1;
            $otherchars = $2;
            my $firstchardec = hex ($firstchar);
            if   ( 0 == $firstchardec % 2 ) { $firstchardec++; }
            else                            { $firstchardec--; }
            $firstchar = sprintf ( "%01X", $firstchardec );
            push ( @returndevs, "$firstchar" . "$otherchars" );
        }
    }
    return @returndevs;
}

sub emc_create_pairfile {
    ## Input @SRCDEVS
    ## writes a pairfile in the format
    ## SOURCE CLONE
    my (@srcdevs)      = @_;
    my @pairfile_clone = ();
    my @pairfile_rep   = ();

    ## Only running if pairfile_clone hasn't been created yet
    if ( !defined $emcfg{pairfile_clone} ) {
        my $created_pair_clone = 0;    ## Tracks if we created anything

        ## Grab our clone devices
        my @clndevs = emc_get_clones (@srcdevs);

        ## If we are a snapshot use the same source and clones
        if ( defined $emcopts{snapshot} ) {
            emc_status ( "info", "-snapshot detected, matching source and clones" );
            @clndevs = @srcdevs;
        }

        bailout ( 60, "Could not find matching clones for all devices" ) if ( scalar (@srcdevs) != scalar (@clndevs) );

        ## Quick Header
        push ( @pairfile_clone, "## Created automatically by $0" );
        push ( @pairfile_clone, "## This file is used by clone scripts" );
        if ( $emcfg{primary} ) {
            push ( @pairfile_clone, "## Should only be run at PRIMARY SITE" );
        }
        else {
            push ( @pairfile_clone, "## Should only be used at SECONDARY SITE" );
        }

        ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_pairfile_clone_20120201_999
        $emcfg{pairfile_clone} =
          "$emcfg{sfdc}" . "_$emcopts{name}" . "_pairfile_clone_" . shortdate . "_$emcfg{sessionid}";

        for ( my $i = 0; $i < scalar (@srcdevs); $i++ ) {
            ## Primary site (as well as p2p) we'll use 6000 7000
            if ( $emcfg{primary} || $emcopts{p2p} ) {
                $created_pair_clone++;
                push ( @pairfile_clone, "$srcdevs[$i] $clndevs[$i]" );
            }
            else {
                ## Secondary (non-p2p) site we'll use 7000 6000
                $created_pair_clone++;
                push ( @pairfile_clone, "$clndevs[$i] $srcdevs[$i]" );
            }
        }

        ## Create our Pairfile
        if ($created_pair_clone) {
            create_output_file ( $emcfg{pairfile_clone}, $emcfg{user_uid}, @pairfile_clone );
        }
        else {
            emc_status ( "warn", "No pairs found for clone pairfile. Skipping." );
        }

    }
    else {
        emc_status ( "info", "Pairfile $emcfg{pairfile_clone} already created, not doing it again" );
    }

    ## Only running if repl pairfile hasn't been created yet
    if ( !defined $emcfg{pairfile_rep} ) {
        my $created_pair_rep = 0;    ## Tracks if we created anything

        ## Grab our clone devices
        ## yeah we should probably not do this a second time in this routine
        my @clndevs = emc_get_clones (@srcdevs);

        ## If we are a snapshot use the same source and clones
        if ( defined $emcopts{snapshot} ) {
            emc_status ( "info", "-snapshot detected, matching source and clones" );
            @clndevs = @srcdevs;
        }

        ## Quick Header
        push ( @pairfile_rep, "## Created automatically by $0" );
        push ( @pairfile_rep, "## This file is used by the srdf script - for replication" );
        if ( $emcfg{primary} ) {
            push ( @pairfile_rep, "## Should only be run at PRIMARY SITE" );
        }
        else {
            push ( @pairfile_rep, "## Should only be used at SECONDARY SITE" );
        }

        ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_pairfile_rep_20120201_999
        $emcfg{pairfile_rep} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_pairfile_rep_" . shortdate . "_$emcfg{sessionid}";

        if ( scalar (@srcdevs) != scalar (@clndevs) ) {
            bailout ( 60, "Could not find matching clones for all devices" );
        }

        for ( my $i = 0; $i < scalar (@srcdevs); $i++ ) {
            ## Primary site we'll use 6000 6000 for p2p, 6000 7000 otherwise
            ## No file for secondary
            if ( $emcfg{primary} ) {
                $created_pair_rep++;
                push ( @pairfile_rep, "$srcdevs[$i] " . ( $emcopts{p2p} ? "$srcdevs[$i]" : "$clndevs[$i]" ) );
            }
            if ( ! $emcfg{primary} && $emcopts{'3dc'} ) { ## Create the pair file on DR if it is 3dc alloc
                $created_pair_rep++;
                push ( @pairfile_rep, "$srcdevs[$i] " . ( $emcopts{p2p} ? "$srcdevs[$i]" : "$clndevs[$i]" ) );
            }
        }

        ## Create our Pairfile
        if ($created_pair_rep) {
            create_output_file ( $emcfg{pairfile_rep}, $emcfg{user_uid}, @pairfile_rep );
        }
        else {
            emc_status ( "warn", "No pairs found for replication pairfile. Skipping." ) if ($emcfg{primary});
        }
    }
    else {
        emc_status ( "info", "Pairfile $emcfg{pairfile_rep} already created, not doing it again" );
    }
}

sub emc_get_rdfinfo_vmax3 {
    my ( $array_partner_type ) = @_; ## It will have either local or remote
    my @rdfRAoutput = safesymcli ( 0, "symcfg -sid $emcfg{sid} list -RA all" );
    my ($rdfport, $rdfportnum, $arraysid, $rdfg, $rdfline, %rdfcount, %arr_partner);
    foreach (@rdfRAoutput) {
       $rdfline=0; #Set RDF Line match to False, if we find regex match we set it to true
       if (/^RF-(\d+E)\s+(\d{1,2})\s(\d{12})\s+(\d{1,2})/) {
            $rdfport    = lc($1);
            $rdfportnum = $2;
            $arraysid   = $3;
            $rdfg       = $4;
            $rdfline    = 1;
       }
       if (/^\s+(\d{1,2})\s(\d{12})\s+(\d{1,2})/) {
            $rdfportnum = $1;
            $arraysid   = $2;
            $rdfg       = $3;
            $rdfline    = 1;
       }
       if ($rdfline) {
            $rdfportnum = $rdfport . ":" . $rdfportnum;
            if ( $rdfcount{$arraysid}{$rdfg}{'rdfPorts'} ) {
                 $rdfcount{$arraysid}{$rdfg}{'rdfPorts'} = $rdfcount{$arraysid}{$rdfg}{'rdfPorts'} . "," . $rdfportnum;
            } else {
                 $rdfcount{$arraysid}{$rdfg}{'rdfPorts'} = $rdfportnum;
            }
       }
    }
    my $min_path=99;
    my $max_path=0;
    my $array_count=0;
    my $local_array;
    my $remote_array;
    foreach $arraysid ( sort keys %rdfcount ) {
       $array_count++;
       $rdfg = (sort keys %{$rdfcount{$arraysid}})[0];
       my @LIST = split (/\,/, $rdfcount{$arraysid}{$rdfg}{'rdfPorts'});
       my $paths = $#LIST;
       if ( $paths < $min_path ) {
           $arr_partner{'local'}{$arraysid}{'rdfPorts'} = $rdfcount{$arraysid}{$rdfg}{'rdfPorts'} ;
           $min_path = $paths;
           $local_array=$arraysid;
       }
       if ( $paths > $max_path ) {
           $arr_partner{'remote'}{$arraysid}{'rdfPorts'} = $rdfcount{$arraysid}{$rdfg}{'rdfPorts'} ;
           $max_path = $paths;
           $remote_array=$arraysid;
       }
    }
    if ( $array_count == 0 ) {
        bailout ( 80, "Unable to determine any array pair." );
    } elsif ( $array_count == 1 ) {
        if ( $array_partner_type eq "remote" ) {
             #$arraysid = (keys %{$arr_partner{$array_partner_type}})[0];
             $arraysid = $remote_array;
             $emcfg{array_pair} = $arraysid;
             $emcfg{local_rdf_dirs} = $arr_partner{$array_partner_type}{$arraysid}{'rdfPorts'};
             $emcfg{remote_rdf_dirs} = $arr_partner{$array_partner_type}{$arraysid}{'rdfPorts'};
        } else {
             bailout ( 80, "Could find only ONE array pair, can't determine local vs remote partner. " );
        }
    } elsif ( $array_count > 2 ) {
        bailout ( 80, "Too many array pairs detected, unable to determine correct array partner. " );
    } else {
        #$arraysid = (keys %{$arr_partner{$array_partner_type}})[0];
        if ( $array_partner_type eq "remote" ) {
             $arraysid = $remote_array;
        } else {
             $arraysid = $local_array;
        }
        $emcfg{array_pair} = $arraysid;
        $emcfg{local_rdf_dirs} = $arr_partner{$array_partner_type}{$arraysid}{'rdfPorts'};
        $emcfg{remote_rdf_dirs} = $arr_partner{$array_partner_type}{$arraysid}{'rdfPorts'};
    }
    ## Gather rdf output from this array for determing available RDFG number & label
    my @rdfgoutput = safesymcli ( 0, "symcfg -sid $emcfg{sid} list -RDFG all" );

    foreach (@rdfgoutput) {
        # regex to Match below pattern
        # RA-Grp  sec  RA-Grp  SymmID       ST    Name    LPDS CHTM Cfg CSRM  time  Pri
        # ------------ --------------------- --------------------------- ----- ----- ---
        #   1 ( 0)  10   1 ( 0) 000196801025 OD grp0       XX.. ..X. F-S -IS-     15  33
        #  10 ( 9)  10  10 ( 9) 000196801025 OD cs21-dgs   XX.. ..X. F-S .AS-     15  33
        #
        if (/^\s+(\d{1,2}).*\s+(\d{12})\s+\w+\s+(.{10})/) {
            my $thisrdf_num   = $1;
            my $array_partner = $2;
            my $thisrdf_name  = stripit ($3);

            ## saves this rdf info
            if ( !defined $rdf_info{$thisrdf_num} ) { $rdf_info{$thisrdf_num} = $thisrdf_name; }
        }
    }
}

sub emc_get_rdfinfo {
    ## Gathers rdf info and stores some info
    ## $emcfg{array_pair} is created here and used for RDF work and associating symdg info
    ## We will only use array RDFG 0, 60 or 61 to determine our partner array in case the array talks to extra during a split

    ## Gather rdf output from this array
    my @rdfgoutput = safesymcli ( 0, "symcfg -sid $emcfg{sid} list -RDFG all" );

    foreach (@rdfgoutput) {
        ## Added another regex to match the new output format
        if ( (/^\s+(\d{1,2}).{21}(.{12})\s.\s(.{1,10})/) || (/^\s+(\d{1,2}).{19}(.{12}).{4}(.{1,10})/) ) {
            my $thisrdf_num   = $1;
            my $array_partner = $2;
            my $thisrdf_name  = stripit ($3);

            ## Save partner array we only want pairs from group 1, 60 or 61 in case a split is in progress
            if (   ( !defined $emcfg{array_pair} )
                && ( ( $thisrdf_num == 60 ) || ( $thisrdf_num == 61 ) || ( $thisrdf_num == 1 ) ) )
            {
                $emcfg{array_pair} = $array_partner;
            }

            ## saves this rdf info
            if ( !defined $rdf_info{$thisrdf_num} ) { $rdf_info{$thisrdf_num} = $thisrdf_name; }
        }
    }
    ## Warn if we don't find rdfg 60 or 61
    if ( !defined $emcfg{array_pair} ) {
        bailout ( 80, "RDF Group 1, 60 or 61 MUST be present to determine array pair." );
    }
}

#############################################
## Shared Subroutines by both DMX and VMAX ##
#############################################
sub emc_run_metas {
    ## Input (width,@device_list)
    ## We will make the metas "width" wide e.g. 16 will create (16 way metas) the default for SFDC
    ## called by emc_main

    my ( $metawidth, @device_list ) = @_;
    my @metacmds     = ();    ## Stores meta commands
    my $created_meta = 0;     ## Tracks if we actually created anything

    if ( $metawidth > 1 ) {
        $metawidth--;
    }                         ## We are going to incriment based on this, and we want to take out the meta head
    else { emc_status ( "warn", "emc_main called with a width less than 2, cannot create 1 way metas" ); return; }

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_meta_20120201_999
    $emcfg{metafile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_meta_" . shortdate . "_$emcfg{sessionid}";

    ## Human Header ##
    @metacmds =
      ( @metacmds, symconfigure_human_header ( $emcfg{metafile} ) )
      ;                       ## Adds the human header to our current output array

    ## Constarnation Header ##
    push ( @metacmds, "##Constarnation:CMD:153:$SYMCLI/symconfigure -sid $emcfg{sid} -f $emcfg{metafile} commit -nop" );
    push ( @metacmds, "##Constarnation:MUST:The configuration change session has successfully completed" );
    push ( @metacmds, "##Constarnation:NEVER:The configuration change session has failed" );

    ## If we are doing clones we need to make those here too
    if ( defined $emcopts{clone} ) {
        my @clonedevs = emc_get_clones (@device_list);    ## First we get our clones
        @device_list = ( @device_list, @clonedevs );      ## Then we shove them onto the end of our list
    }

    ## Lets make some metas
    foreach my $thisdev (@device_list) {
        ## Only want to make metas out of devices that aren't metas already
        if ( ( defined $device_info{$thisdev}{meta_type} ) && ( $device_info{$thisdev}{meta_type} eq "NONE" ) ) {

            ## Check each member to make sure not alrady a member
            my $dirtymembers = 0;
            my $start        = hex ($thisdev) + 1;
            my $end          = $start + $metawidth - 1;
            for ( my $i = $start; $i < $end; $i++ ) {
                my $thishextest = sprintf ( "%04X", $i );
                if ( !defined $device_info{$thishextest}{meta_type} ) {
                    emc_status ( "warn", "unable to determine meta type of potential member $thishextest" );
                    $dirtymembers++;
                }
                elsif ( $device_info{$thishextest}{meta_type} ne "NONE" ) {
                    $dirtymembers++;
                    emc_status ( "warn",
                        "Cannot create meta from $thisdev because $thishextest is already part of meta" );

                    ## Lets now set this guy to a meta member so we don't grab it for future luns
                    $device_info{$thishextest}{meta_type} = "member";
                }
            }

            if ( !$dirtymembers ) {
                $created_meta++;    ## We created something
                my $first_member = sprintf ( "%04X", hex ($thisdev) + 1 );    ## First member is this device + 1
                my $last_member =
                  sprintf ( "%04X", hex ($thisdev) + $metawidth );    ## Ending meta is width - 1 away from the head
                push ( @metacmds, "Form meta from dev $thisdev, config=striped;" );
                push ( @metacmds, " add dev $first_member:$last_member to meta $thisdev;" );
            }
        }
        else {
            emc_status ( "warn", "Device $thisdev is already part of a meta, not going to create it" );
        }
    }

    ## Create our Meta File
    if ($created_meta) { create_output_file ( $emcfg{metafile}, $emcfg{user_uid}, @metacmds ); }
    else {
        emc_status ( "warn", "Did not create any meta devices, not writing file." );
        undef $emcfg{metafile};
    }
}

sub emc_run_convert {
    ## Converts the device to the appropriate type. e.g. 2-Way-Mir or TDEV+BCV
    my (@device_list) = @_;
    my @convertcmds   = ();
    my $convert_yet   = 0;    ## Tracks if we've converted anything
    ## Variables for DG array
    my @dgconvertcmds = ();
    my $dgconvert_yet = 0;    ## Tracks if we've converted anything for DG
    my ( $thisdev, $thisdev_type );
    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_convert_20120201_999
    $emcfg{convertfile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_convert_" . shortdate . "_$emcfg{sessionid}";

    ## Human Header ##
    @convertcmds =
      ( @convertcmds, symconfigure_human_header ( $emcfg{convertfile} ) )
      ;                       ## Adds the human header to our current output array

    ## Constarnation Header ##
    push ( @convertcmds,
        "##Constarnation:CMD:253:$SYMCLI/symconfigure -sid $emcfg{sid} -f $emcfg{convertfile} commit -nop" );
    push ( @convertcmds, "##Constarnation:MUST:The configuration change session has successfully completed" );
    push ( @convertcmds, "##Constarnation:NEVER:The configuration change session has failed" );

    ## For 3dc alloc create another cmd file for DG array
    if ( $emcopts{'3dc'} ) {
         $emcfg{dgconvertfile} = "$emcfg{sfdc}" . "_$emcopts{dgname}" . "_convert_" . shortdate . "_$emcfg{sessionid}";
         ## Human Header ##
         @dgconvertcmds =
           ( @dgconvertcmds, symconfigure_human_header ( $emcfg{dgconvertfile} ) )
           ;                       ## Adds the human header to our current output array

         ## Constarnation Header ##
         push ( @dgconvertcmds,
             "##Constarnation:CMD:283:$SYMCLI/symconfigure -sid $emcfg{partner_sid} -f $emcfg{dgconvertfile} commit -nop" );
         push ( @dgconvertcmds, "##Constarnation:MUST:The configuration change session has successfully completed" );
         push ( @dgconvertcmds, "##Constarnation:NEVER:The configuration change session has failed" );
    }

    ## See if any of the devices need to have dynamic RDF enabled
    my @combined_list = @device_list;
    if ( $emcopts{clone} ) { @combined_list = ( @combined_list, emc_get_clones (@device_list) ); }
    foreach (@combined_list) {
        if ( ( defined $device_info{$emcfg{sid}}{$_}{dynamic_rdf} ) && ( $device_info{$emcfg{sid}}{$_}{dynamic_rdf} eq "no" ) ) {
            emc_status ( "info", "Dynmaic RDF disabled for device $_, adding attribute to convert file" );
            push ( @convertcmds, "set dev $_ attribute=dyn_rdf;" );
            $convert_yet++;
        }
    }

    ## Primary Site
    if ( $emcfg{primary} || $emcopts{p2p} ) {
        ## Loop through our source devices
        foreach (@device_list) {
            $thisdev = $_;
            ## If we find an RDF device, don't even bother trying to convert it, just display a soft warning and move on
            if ( ( defined $device_info{$emcfg{sid}}{$thisdev}{device_type} ) && ( $device_info{$emcfg{sid}}{$thisdev}{device_type} =~ /^RDF/ ) )
            {
                emc_status ( "warn", "Not converting $emcfg{sid} : $thisdev. Not in a convertable state." );
            }
            else {
                if ( !defined $device_info{$emcfg{sid}}{$thisdev}{device_type} ) {
                    bailout ( 50, "Unable to determine device_type for $emcfg{sid}: $thisdev . Cannot convert" );
                }
                $thisdev_type = $device_info{$emcfg{sid}}{$thisdev}{device_type};

                ## If the device exists in $primary_device_types then we know it's already good
                if ( !defined $device_type_labels{$thisdev_type} ) {
                    bailout ( 50, "Not sure how to convert $thisdev_type ." );
                }
                if ( defined $primary_device_types{$thisdev_type} ) {
                    emc_status ( "info", "Not converting $thisdev . Already set to $thisdev_type." );
                }
                else {
                    $convert_yet++;
                    push ( @convertcmds, "convert dev $thisdev to $device_type_labels{$thisdev_type};" );
                }
            }
        }

        ## If we have 3dc allocation, then verify source devices for DG arrays
        if ( $emcopts{'3dc'} ) {
            foreach (@device_list) {
                $thisdev = $_;
                ## If we find an RDF device, don't even bother trying to convert it, just display a soft warning and move on
                if ( ( defined $device_info{$emcfg{partner_sid}}{$thisdev}{device_type} ) && ( $device_info{$emcfg{partner_sid}}{$thisdev}{device_type} =~ /^RDF/ ) )
                {
                    emc_status ( "warn", "Not converting $emcfg{partner_sid} : $thisdev. Not in a convertable state." );
                }
                else {
                    if ( !defined $device_info{$emcfg{partner_sid}}{$thisdev}{device_type} ) {
                        bailout ( 50, "Unable to determine device_type for $emcfg{partner_sid}: $thisdev . Cannot convert" );
                    }
                    $thisdev_type = $device_info{$emcfg{partner_sid}}{$thisdev}{device_type};

                    ## If the device exists in $primary_device_types then we know it's already good
                    if ( !defined $device_type_labels{$thisdev_type} ) {
                        bailout ( 50, "Not sure how to convert $thisdev_type ." );
                    }
                    if ( defined $primary_device_types{$thisdev_type} ) {
                        emc_status ( "info", "Not converting $thisdev . Already set to $thisdev_type." );
                    }
                    else {
                        $dgconvert_yet++;
                        push ( @dgconvertcmds, "convert dev $thisdev to $device_type_labels{$thisdev_type};" );
                    }
                }
            }
        }

        ## Time for clones, if we're doing them
        if ( $emcopts{clone} ) {
            my @clone_list = emc_get_clones (@device_list);    ## First we get our clones

            ## Loop through clone devices
            foreach (@clone_list) {
                $thisdev = $_;
                ## If we find an RDF device, don't even bother trying to convert it, just display a soft warning and move on
                if (   ( defined $device_info{$emcfg{sid}}{$thisdev}{device_type} )
                    && ( $device_info{$emcfg{sid}}{$thisdev}{device_type} =~ /^RDF/ ) )
                {
                    emc_status ( "warn", "Not converting $thisdev. Not in a convertable state." );
                }
                else {
                    if ( !defined $device_info{$emcfg{sid}}{$thisdev}{device_type} ) {
                        bailout ( 50, "Unable to determine device_type for clone $thisdev . Cannot convert" );
                    }
                    $thisdev_type = $device_info{$emcfg{sid}}{$thisdev}{device_type};

                    ## We'll compare clones to $secondary_device_types to see if they are good
                    if ( defined $secondary_device_types{$thisdev_type} ) {
                        emc_status ( "info", "Not converting $thisdev . Already set to $thisdev_type." );
                    }
                    elsif ( defined $device_type_labels{$thisdev_type} ) {
                        $convert_yet++;
                        push ( @convertcmds, "convert dev $thisdev to $device_type_labels{$thisdev_type};" );
                    }
                    else { bailout ( 20, "Clone type $thisdev_type not valid." ); }
                }
            }
        }
    }

    ## Secondary Site
    ## At secondary site the "clones" are the devices shown to the hosts.  So we basically need to reverse our logic to make sue the "BCV" devices are shown to the hosts
    else {
        ## Loop through our source devices
        foreach (@device_list) {
            $thisdev = $_;
            ## If we find an RDF device, don't even bother trying to convert it, just display a soft warning and move on
            if ( ( defined $device_info{$emcfg{sid}}{$thisdev}{device_type} ) && ( $device_info{$emcfg{sid}}{$thisdev}{device_type} =~ /^RDF/ ) )
            {
                emc_status ( "warn", "Not converting $thisdev. Not in a convertable state." );
            }
            else {
                if ( !defined $device_info{$emcfg{sid}}{$thisdev}{device_type} ) {
                    bailout ( 50, "Unable to determine device_type for $thisdev . Cannot convert" );
                }
                $thisdev_type = $device_info{$emcfg{sid}}{$thisdev}{device_type};

                ## If the device exists in $primary_device_types then we know it's already good
                if ( defined $secondary_device_types{$thisdev_type} ) {
                    emc_status ( "info", "Not converting $thisdev . Already set to $thisdev_type." );
                }
                else {
                    $convert_yet++;
                    push ( @convertcmds, "convert dev $thisdev to $device_type_labels{$thisdev_type};" );
                }
            }
        }

        ## If we have 3dc allocation, then verify source devices for DG arrays
        if ( $emcopts{'3dc'} ) {
            foreach (@device_list) {
                $thisdev = $_;
                ## If we find an RDF device, don't even bother trying to convert it, just display a soft warning and move on
                if ( ( defined $device_info{$emcfg{partner_sid}}{$thisdev}{device_type} ) && ( $device_info{$emcfg{partner_sid}}{$thisdev}{device_type} =~ /^RDF/ ) )
                {
                    emc_status ( "warn", "Not converting $thisdev. Not in a convertable state." );
                }
                else {
                    if ( !defined $device_info{$emcfg{partner_sid}}{$thisdev}{device_type} ) {
                        bailout ( 50, "Unable to determine device_type for $thisdev . Cannot convert" );
                    }
                    $thisdev_type = $device_info{$emcfg{partner_sid}}{$thisdev}{device_type};

                    ## If the device exists in $primary_device_types then we know it's already good
                    if ( defined $secondary_device_types{$thisdev_type} ) {
                        emc_status ( "info", "Not converting $thisdev . Already set to $thisdev_type." );
                    }
                    else {
                        $convert_yet++;
                        push ( @convertcmds, "convert dev $thisdev to $device_type_labels{$thisdev_type};" );
                    }
                }
            }
        }

        ## Time for clones, if we're doing them
        if ( $emcopts{clone} ) {
            my @clone_list = emc_get_clones (@device_list);    ## First we get our clones

            ## Loop through clone devices
            foreach (@clone_list) {
                $thisdev = $_;
                ## If we find an RDF device, don't even bother trying to convert it, just display a soft warning and move on
                if (   ( defined $device_info{$emcfg{sid}}{$thisdev}{device_type} )
                    && ( $device_info{$emcfg{sid}}{$thisdev}{device_type} =~ /^RDF/ ) )
                {
                    emc_status ( "warn", "Not converting $thisdev. Not in a convertable state." );
                }
                else {
                    if ( !defined $device_info{$emcfg{sid}}{$thisdev}{device_type} ) {
                        bailout ( 50, "Unable to determine device_type for clone $thisdev . Cannot convert" );
                    }
                    $thisdev_type = $device_info{$emcfg{sid}}{$thisdev}{device_type};

                    ## We'll compare clones to $secondary_device_types to see if they are good
                    if ( defined $primary_device_types{$thisdev_type} ) {
                        emc_status ( "info", "Not converting $thisdev . Already set to $thisdev_type." );
                    }
                    else {
                        $convert_yet++;
                        push ( @convertcmds, "convert dev $thisdev to $device_type_labels{$thisdev_type};" );
                    }
                }
            }
        }
    }

    ## Create our Convert File
    if ($convert_yet) { create_output_file ( $emcfg{convertfile}, $emcfg{user_uid}, @convertcmds ); }
    else {
        emc_status ( "warn", "Did not need to convert any device types, not writing file." );
        undef $emcfg{convertfile};
    }

    ## Create DG Convert File
    if ($dgconvert_yet) { create_output_file ( $emcfg{dgconvertfile}, $emcfg{user_uid}, @dgconvertcmds ); }
    else {
        emc_status ( "warn", "Did not need to convert any device types for DG array, not writing file." );
        undef $emcfg{dgconvertfile};
    }
}

sub emc_run_clone {
    ## Will create clonefile
    ## Creates clone pair then associates the bcv's to the group
    my (@device_list) = @_;

    if ( !@device_list ) { bailout ( 80, "emc_run_clone recieved empty device_list" ); }

    my @clonecmds      = ();
    my $bcv_associated = 0;    ## Tracks if we've associated any bcvs
    my ( $thisdev, $thisdev_type );

    ## Get our Clones
    my @clone_list = emc_get_clones (@device_list);    ## First we get our clones

    ## If we haven't done so already, create our pairfile
    if ( !defined $emcfg{pairfile_clone} ) { emc_create_pairfile (@device_list); }

    ## Ensure the pairfile exists
    if ( !defined $emcfg{pairfile_clone} ) { bailout ( 40, "pairfile creation failed, unable to continue." ); }
    if ( !-e $emcfg{pairfile_clone} ) {
        emc_status ( "warn", "emc_run_clone unable to locate pairfile, won't be able to generate clone script" );
    }
    else {

        ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_clone_20120201_999.sh
        $emcfg{clonefile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_clone_" . shortdate . "_$emcfg{sessionid}" . ".sh";

        ## Human Header ##
        push ( @clonecmds, "## Execute this as a shell script : 'sudo ./$emcfg{clonefile}'" );
        push ( @clonecmds, "## " . logtime . " Created automatically via $0" );
        push ( @clonecmds, "##" );

        ## Constarnation Header
        push ( @clonecmds, "##Constarnation:CMD:653:./$emcfg{clonefile}" );
        push ( @clonecmds, "##Constarnation:MUST:'Create' operation successfully executed" );
        push ( @clonecmds, "##Constarnation:MUST:'Activate' operation successfully executed" );

        ## Clone Create
        push ( @clonecmds,
            "$SYMCLI/symclone -sid $emcfg{sid} -file $emcfg{pairfile_clone} create -precopy -differential -nop" );

        ## Sleep Command just in to give the create a little time
        push ( @clonecmds, "echo \"Waiting 20 seconds before activate\"" );
        push ( @clonecmds, "sleep 20" );

        ## Activate Clone
        push ( @clonecmds, "$SYMCLI/symclone -sid $emcfg{sid} -file $emcfg{pairfile_clone} activate -consistent -nop" );

        ## Create our Clone File
        create_output_file ( $emcfg{clonefile}, $emcfg{user_uid}, @clonecmds );
    }
}

sub emc_run_replication {
    ## Will
    my ($format_option, @device_list) = @_;
    my @replcmds = ();

    ## Make sure our device_list is good
    if ( !@device_list ) { bailout ( 80, "emc_run_replication recieved empty device_list" ); }

    if ( !$emcfg{primary} ) {
        emc_status ( "info", "Replication cannot be run at the secondary site, skipping." );
        return;
    }

    ## Pull RDF info if we don't already have our array pair.. **Dont need it if we are only generating simple call back to ourselves**
    #if (! defined $emcfg{array_pair}) { emc_get_rdfinfo; }

    ## Get our Clones  .. BECAUSE WE MUST HAVE A VALID PAIRFILE CREATED ALREADY TO DO THIS
    my @clone_list = emc_get_clones (@device_list);    ## First we get our clones

    ## If this is a snapshot we use the same devices for primary and secondary
    if ( defined $emcopts{snapshot} ) { @clone_list = @device_list; }

    ## If we haven't done so already, create our pairfile
    if ( !defined $emcfg{pairfile_rep} ) { emc_create_pairfile (@device_list); }

    ## Ensure the pairfile exists
    if ( !defined $emcfg{pairfile_rep} ) { bailout ( 40, "pairfile creation failed, unable to continue." ); }
    if ( !-e $emcfg{pairfile_rep} ) {
        emc_status ( "warn", "emc_run_replication unable to locate pairfile, won't be able to generate RDF script" );
    }
    else {
        ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_replication_20120201_999.sh
        $emcfg{replicationfile} =
          "$emcfg{sfdc}" . "_$emcopts{name}" . "_replication_" . shortdate . "_$emcfg{sessionid}" . ".sh";

        ## Human Header ##
        push ( @replcmds, "## Execute this as a shell script : 'sudo ./$emcfg{replicationfile}'" );
        push ( @replcmds, "## WARNING: This script can take a very long time to execute. Will fail after 3 days." );
        push ( @replcmds, "## " . logtime . " Created automatically via $0" );
        push ( @replcmds, "##" );

        my $format_line="";
        ## Constarnation Header
        if ( $format_option eq "true" ) {
            push ( @replcmds, "##Constarnation:CMD:453:./$emcfg{replicationfile}" );
            emc_status ( "INFO", "Using -format option for SRDF setup, please pay close attention to Constarnation #, as srdf replication needs to be done before mapping of devs." );
            $format_line="--format"
        } else {
            push ( @replcmds, "##Constarnation:CMD:853:./$emcfg{replicationfile}" );
        }
        push ( @replcmds, "##Constarnation:NEVER:ERROR" );

        ## Lets get some absolute paths so that we call the right thing
        if ( !defined $emcfg{this_script} )      { $emcfg{this_script}      = abs_path ($0); }
        if ( !defined $emcfg{abs_pairfile_rep} ) { $emcfg{abs_pairfile_rep} = abs_path ( $emcfg{pairfile_rep} ); }

        ## One liner, just going to call oursevles back with the -exec_srdf flag
        my $base_cmd =
"$emcfg{this_script} --asn $emcfg{sid} --pairfile $emcfg{abs_pairfile_rep} --exec_srdf --name $emcopts{name} --primary --sfdc $emcfg{sfdc} --session $emcfg{sessionid} $format_line --verbose";
        if ( $emcopts{'3dc'} ) {
            push ( @replcmds, "$base_cmd" );
        } else {
            if ( defined $emcfg{local_rdf_dirs} ) {
              push ( @replcmds,
                "$base_cmd --local_rdf_dirs $emcfg{local_rdf_dirs} --remote_rdf_dirs $emcfg{remote_rdf_dirs}" );
            } else { push ( @replcmds, "$base_cmd" ); }
        }

        ## Create our Replication File
        create_output_file ( $emcfg{replicationfile}, $emcfg{user_uid}, @replcmds );
    }
}

sub emc_run_replication_dg {
    ## Replication for local 2 arrays DB & DG
    my ($format_option, @device_list) = @_;
    my @dgreplcmds = ();
    my $siteType;

    ## Make sure our device_list is good
    if ( !@device_list ) { bailout ( 80, "emc_run_replication recieved empty device_list" ); }

    ## If we haven't done so already, create our pairfile
    if ( !defined $emcfg{pairfile_rep} ) { emc_create_pairfile (@device_list); }

    ## Set up the site type primary or secondary
    if ( $emcfg{primary} ) {
        $siteType="--primary";
    } else {
        $siteType="--secondary";
    }

    ## Ensure the pairfile exists
    if ( !defined $emcfg{pairfile_rep} ) { bailout ( 40, "pairfile creation failed, unable to continue." ); }
    if ( !-e $emcfg{pairfile_rep} ) {
        emc_status ( "warn", "emc_run_replication unable to locate pairfile, won't be able to generate RDF script" );
    }
    else {
        ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_replication_20120201_999.sh
        $emcfg{dgreplicationfile} =
          "$emcfg{sfdc}" . "_$emcopts{dgname}" . "_replication_" . shortdate . "_$emcfg{sessionid}" . ".sh";

        ## Human Header ##
        push ( @dgreplcmds, "## Execute this as a shell script : 'sudo ./$emcfg{dgreplicationfile}'" );
        push ( @dgreplcmds, "## WARNING: This script can take a very long time to execute. Will fail after 3 days." );
        push ( @dgreplcmds, "## " . logtime . " Created automatically via $0" );
        push ( @dgreplcmds, "##" );

        my $format_line="";
        ## Constarnation Header
        if ( $format_option eq "true" ) {
            push ( @dgreplcmds, "##Constarnation:CMD:463:./$emcfg{dgreplicationfile}" );
            emc_status ( "INFO", "Using -format option for SRDF setup, please pay close attention to Constarnation #, as srdf replication needs to be done before mapping of devs." );
            $format_line="--format"
        } else {
            push ( @dgreplcmds, "##Constarnation:CMD:863:./$emcfg{dgreplicationfile}" );
        }
        push ( @dgreplcmds, "##Constarnation:NEVER:ERROR" );

        ## Lets get some absolute paths so that we call the right thing
        if ( !defined $emcfg{this_script} )      { $emcfg{this_script}      = abs_path ($0); }
        if ( !defined $emcfg{abs_pairfile_rep} ) { $emcfg{abs_pairfile_rep} = abs_path ( $emcfg{pairfile_rep} ); }

        ## One liner, just going to call oursevles back with the -exec_srdf flag
        my $base_cmd =
"$emcfg{this_script} --asn $emcfg{sid} --pairfile $emcfg{abs_pairfile_rep} --exec_srdf --name $emcopts{dgname} $siteType --sfdc $emcfg{sfdc} --session $emcfg{sessionid} $format_line --verbose --3dc";
        push ( @dgreplcmds, "$base_cmd" );

        ## Create our Replication File
        create_output_file ( $emcfg{dgreplicationfile}, $emcfg{user_uid}, @dgreplcmds );
    }
}

sub emc_run_symdg_dg {
    ## Creates symdg group and populates it
    ## WARNING This will only work if replication and clones have already been started
    ## Input @device_list of standard devices
    ## Called on by emc_main
    my (@device_list) = @_;    ## Holds devices assigned to host
    if ( !@device_list ) { bailout ( 80, "emc_run_symdg recieved empty device_list" ); }
    my @dgsymdgcmds        = ();    ## holds commands for creating symdg and assigning devs
    my $bcv_associated   = 0;     ## Tracks if we've associated any bcvs
    my $symld_associated = 0;     ## Tracks if we've associated any standards
    my ($array_suffix);           ## Holds the last 3 digits of array serial, used symdg device names
    my $symdg_exists = 0;         ## Tracks if our symgroup exists
    my @clone_list;               ## Hold clone devs

    ## Set our symdg name if we havent already
    if ( !defined $emcfg{symdgDG} ) { emc_set_symdg_name; }

    ## Lets see if our symdg alrady exists
    my @symdgoutput = safesymcli ( 0, "symdg list" );
    foreach (@symdgoutput) {
        if (/^\s+$emcfg{symdgDG}\s+R/) {
            $symdg_exists++;
            emc_status ( "info", "symdg group $emcfg{symdgDG} already exists, adding to it" );
        }
    }
    if ( !$symdg_exists ) { emc_status ( "info", "symdg group $emcfg{symdgDG} does not already exist." ); }

    ## Pull RDF info
    if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) { emc_get_rdfinfo_vmax3('local');
        } else { bailout ( 10, "Unsupported array type for local srdf replication setup."); }

    ## Saves array suffix, we just want the last 3 digits Primary site will be this array, secondary site will be partner array
    if ( $emcfg{primary} ) {
        $array_suffix = substr $emcfg{sid}, -3;
    }
    else {
        if ( defined $emcfg{array_pair} ) { $array_suffix = substr $emcfg{array_pair}, -3; }
        else                              { bailout ( 50, "emc_run_symdg unable to determine partner array" ); }
    }

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_symdg_20120201_999.sh
    $emcfg{dgsymdgfile} = "$emcfg{sfdc}" . "_$emcopts{dgname}" . "_symdg_" . shortdate . "_$emcfg{sessionid}" . ".sh";

    ## Human Header ##
    push ( @dgsymdgcmds, "## Execute this as a shell script : 'sudo ./$emcfg{dgsymdgfile}'" );
    push ( @dgsymdgcmds, "## " . logtime . " Created automatically via $0" );
    push ( @dgsymdgcmds, "##" );

    ## Primary/secondary warning
    if   ( $emcfg{primary} ) { push ( @dgsymdgcmds, "## WARNING : This should only be run at PRIMARY SITE" ); }
    else                     { push ( @dgsymdgcmds, "## WARNING : This should only be run at SECONDARY/DR SITE" ); }

    ## Constarnation Header
    push ( @dgsymdgcmds, "##Constarnation:CMD:953:./$emcfg{dgsymdgfile}" );
    push ( @dgsymdgcmds, "##Constarnation:NEVER:The device group already exists" );

    ## Create our symdg and populate it
    if ( $emcfg{symdgDG} ne "NONE" ) {

        ## Primary Site
        if ( $emcfg{primary} ) {
            if ( !$symdg_exists ) { push ( @dgsymdgcmds, "$SYMCLI/symdg create $emcfg{symdgDG} -type RDF2" ); }
            push ( @dgsymdgcmds, "## Dest / R2 / Assigned to host" );
            foreach (@device_list) {
                $symld_associated++;
                push ( @dgsymdgcmds, "echo \"Adding dev $_ to $emcfg{symdgDG}\"" );
                push ( @dgsymdgcmds, "$SYMCLI/symdg -g $emcfg{symdgDG} -sid $emcfg{partner_sid} add dev $_ $array_suffix" . "$_" );
            }
        }
        ## Secondary Site
        else {
            if ( !$symdg_exists ) { push ( @dgsymdgcmds, "$SYMCLI/symdg create $emcfg{symdgDG} -type RDF2" ); }
            push ( @dgsymdgcmds, "## Source / R2" );
            foreach ( $emcopts{p2p} ? @device_list : @clone_list ) {
                ## At secondary site we need to get the "original" disk
                my ($original_disk) = emc_get_clones ($_);
                $symld_associated++;
                push ( @dgsymdgcmds, "echo \"Adding dev $_ to $emcfg{symdgDG}\"" );
                push ( @dgsymdgcmds,
                    "$SYMCLI/symdg -g $emcfg{symdgDG} -sid $emcfg{partner_sid} add dev $_ $array_suffix" . "$original_disk" );
            }
        }
    }

    ## Creates our symdg file
    if ( ($bcv_associated) || ($symld_associated) ) {
        create_output_file ( $emcfg{dgsymdgfile}, $emcfg{user_uid}, @dgsymdgcmds );
    }
    else {
        emc_status ( "warn", "Did not associate any BCVs or Source devices, not writing file." );
        undef $emcfg{dgsymdgfile};
    }
}

sub emc_run_symdg {
    ## Creates symdg group and populates it
    ## WARNING This will only work if replication and clones have already been started
    ## Input @device_list of standard devices
    ## Called on by emc_main
    my (@device_list) = @_;    ## Holds devices assigned to host
    if ( !@device_list ) { bailout ( 80, "emc_run_symdg recieved empty device_list" ); }
    my @symdgcmds        = ();    ## holds commands for creating symdg and assigning devs
    my $bcv_associated   = 0;     ## Tracks if we've associated any bcvs
    my $symld_associated = 0;     ## Tracks if we've associated any standards
    my ($array_suffix);           ## Holds the last 3 digits of array serial, used symdg device names
    my $symdg_exists = 0;         ## Tracks if our symgroup exists
    my @clone_list;               ## Hold clone devs


    ## Set our symdg name if we havent already
    if ( !defined $emcfg{symdg} ) { emc_set_symdg_name; }

    ## Lets see if our symdg alrady exists
    my @symdgoutput = safesymcli ( 0, "symdg list" );
    foreach (@symdgoutput) {
        if (/^\s+$emcfg{symdg}\s+R/) {
            $symdg_exists++;
            emc_status ( "info", "symdg group $emcfg{symdg} already exists, adding to it" );
        }
    }
    if ( !$symdg_exists ) { emc_status ( "info", "symdg group $emcfg{symdg} does not already exist." ); }

    ## Pull RDF info if we don't already have our array pair
    if ( !defined $emcfg{array_pair} ) {
        if ( $emcfg{array_type} eq "VMAX100K" ) { emc_get_rdfinfo_vmax3('remote');
        } else { emc_get_rdfinfo; }
    }

    ## Get our Clones
    if ( $emcfg{clone} ) {
         @clone_list = emc_get_clones (@device_list); }

    ## Saves array suffix, we just want the last 3 digits Primary site will be this array, secondary site will be partner array
    if ( $emcfg{primary} ) {
        $array_suffix = substr $emcfg{sid}, -3;
    }
    else {
        if ( defined $emcfg{array_pair} ) { $array_suffix = substr $emcfg{array_pair}, -3; }
        else                              { bailout ( 50, "emc_run_symdg unable to determine partner array" ); }
    }

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_symdg_20120201_999.sh
    $emcfg{symdgfile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_symdg_" . shortdate . "_$emcfg{sessionid}" . ".sh";

    ## Human Header ##
    push ( @symdgcmds, "## Execute this as a shell script : 'sudo ./$emcfg{symdgfile}'" );
    push ( @symdgcmds, "## " . logtime . " Created automatically via $0" );
    push ( @symdgcmds, "##" );

    ## Primary/secondary warning
    if   ( $emcfg{primary} ) { push ( @symdgcmds, "## WARNING : This should only be run at PRIMARY SITE" ); }
    else                     { push ( @symdgcmds, "## WARNING : This should only be run at SECONDARY/DR SITE" ); }

    ## Constarnation Header
    push ( @symdgcmds, "##Constarnation:CMD:953:./$emcfg{symdgfile}" );
    push ( @symdgcmds, "##Constarnation:NEVER:The device group already exists" );

    ## Create our symdg and populate it
    if ( $emcfg{symdg} ne "NONE" ) {

        ## Primary Site
        if ( $emcfg{primary} ) {
            if ( !$symdg_exists ) { push ( @symdgcmds, "$SYMCLI/symdg create $emcfg{symdg} -type RDF1" ); }
            push ( @symdgcmds, "## Source / R1 / Assigned to host" );
            foreach (@device_list) {
                $symld_associated++;
                push ( @symdgcmds, "echo \"Adding dev $_ to $emcfg{symdg}\"" );
                push ( @symdgcmds, "$SYMCLI/symdg -g $emcfg{symdg} -sid $emcfg{sid} add dev $_ $array_suffix" . "$_" );
            }
            push ( @symdgcmds, "## Clones" );
            foreach (@clone_list) {
                $bcv_associated++;
                push ( @symdgcmds, "echo \"Adding BCV $_ to $emcfg{symdg}\"" );
                push ( @symdgcmds, "$SYMCLI/symbcv -g $emcfg{symdg} -sid $emcfg{sid} associate dev $_ CLN$_" );
            }
        }
        ## Secondary Site
        else {
            if ( !$symdg_exists ) { push ( @symdgcmds, "$SYMCLI/symdg create $emcfg{symdg} -type RDF2" ); }
            push ( @symdgcmds, "## Source / R2" );
            foreach ( $emcopts{p2p} ? @device_list : @clone_list ) {
                ## At secondary site we need to get the "original" disk
                my ($original_disk) = emc_get_clones ($_);
                $symld_associated++;
                push ( @symdgcmds, "echo \"Adding dev $_ to $emcfg{symdg}\"" );
                push ( @symdgcmds,
                    "$SYMCLI/symdg -g $emcfg{symdg} -sid $emcfg{sid} add dev $_ $array_suffix" . "$original_disk" );
            }
            push ( @symdgcmds, "## Clones / Assigned to host" );
            foreach ( $emcopts{p2p} ? @clone_list : @device_list ) {
                $bcv_associated++;
                push ( @symdgcmds, "echo \"Adding BCV $_ to $emcfg{symdg}\"" );
                push ( @symdgcmds, "$SYMCLI/symbcv -g $emcfg{symdg} -sid $emcfg{sid} associate dev $_ CLN$_" );
            }
        }
    }

    ## Creates our symdg file
    if ( ($bcv_associated) || ($symld_associated) ) {
        create_output_file ( $emcfg{symdgfile}, $emcfg{user_uid}, @symdgcmds );
    }
    else {
        emc_status ( "warn", "Did not associate any BCVs or Source devices, not writing file." );
        undef $emcfg{symdgfile};
    }
}

sub emc_exec_srdf_cmds {
    ## Executes the symrdf commands and looks for errors
    ## Input : Step #   ... Will get the command to run by referencing %exec_srdf hash with the number
    ## Any error code other than zero will bailout of the program all together
    my $failed_step = 0;

    ## Make sure we recieved at least one step
    if ( !defined $exec_srdf{1} ) { bailout ( 10, "emc_exec_srdf_cmds recieved invalid procedure in %exec_srdf." ); }

    ## Run through each step
    foreach my $step ( sort { $a <=> $b } keys %exec_srdf ) {
        if ( ( !$failed_step ) && ( defined $exec_srdf{$step}{desc} ) ) {
            emc_status ( "INFO", $exec_srdf{$step}{desc} );
        }
        if ( ( !$failed_step ) && ( defined $exec_srdf{$step}{cmd} ) ) {
            emc_status ( "info", "running $SYMCLI/" . $exec_srdf{$step}{cmd} );

            ## Run our command for this step
            my @myresults = `$SYMCLI/$exec_srdf{$step}{cmd} 2>&1`;

            my $ecode = $? >> 8;

            ## Houston, we have a problem
            if ( ($?) && ( $ecode != 18 ) ) {
                $failed_step = $step;
                ## This will throw the error out to STDERR
                foreach (@myresults) {    ## This will throw the error out to STDERR
                    my $err = $_;
                    chomp ($err);
                    ## Only print non blank lines
                    if ( !$err =~ /^$/ ) { emc_status ( "ERROR", $err ); }
                }
                emc_status ( "WARNING",
                    "SRDF Did not complete, you will need to run the following commands by hand to finish." );
            }
        }
        if ($failed_step) {
            push ( @emc_logfile, "## Step $step - $exec_srdf{$step}{desc}" );
            push ( @emc_logfile, "$exec_srdf{$step}{cmd}" );
            print "## Step $step - $exec_srdf{$step}{desc}\n";
            print "$exec_srdf{$step}{cmd}\n";
        }
    }

    ## We failed to complete all of our steps, fail out with error code 99
    if ($failed_step) { emc_write_logfile; exit 99; }
}

sub emc_run_exec_srdf {
    ## Runs our SRDF procedure
    ## Pupulates the %exec_srdf  hash with a step and a command, then runs emc_exec_srdf_cmds to execute it
    my $perm_rdfnum  = 0;
    my $matched_base = 0;     ## Tracks if we matched our base name e.g. cs99
    my $name_inuse   = 0;     ## Tracks if our perm rdfg name is in use
    my $open_range   = 10;    ## Looks for an open RDF range for new pods
    my $formatOption = "";    ## Tracks whether to turn on the -format option while createpair or not

    ## FAIL if not at primary site, and it is not 3dc for local srdf
    if ( !$emcfg{primary} && !$emcopts{'3dc'}) { bailout ( 10, "RDF Proocedure can ONLY be run at primary site" ); }

    ## Make sure our pairfile exists
    if    ( !defined $emcopts{pairfile} ) { bailout ( 10, "Unable to determine pairfile, halting." ); }
    elsif ( !-e $emcopts{pairfile} )      { bailout ( 10, "Unable to verify pairfile $emcopts{pairfile}, halting." ); }

    ## Pull RDF info if we don't already have our array pair
    if ( !defined $emcfg{array_pair} ) {
        if ( $emcopts{'3dc'} ) {
             if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) { emc_get_rdfinfo_vmax3('local');
             } else { bailout ( 10, "Unsupported array type for local srdf replication setup."); }
        } else {
             if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) { emc_get_rdfinfo_vmax3('remote');
             } else { emc_get_rdfinfo; }
        }
    }
    ## If no directors specified, use defaults
    if ( !defined $emcfg{local_rdf_dirs} ) {
        if ( !defined $emcfg{array_type} ) { bailout ( 10, "emc_run_exec_srdf unable to determine array_type" ); }
        else {
            emc_status ( "info",
"Using default values for local_rdf_dirs for array type ($emcfg{array_type}): $default_rdf_ports{$emcfg{array_type}}"
            );
            $emcfg{local_rdf_dirs} = $default_rdf_ports{ $emcfg{array_type} };
        }
    }
    if ( !defined $emcfg{remote_rdf_dirs} ) {
        if ( !defined $emcfg{array_type} ) { bailout ( 10, "emc_run_exec_srdf unable to determine array_type" ); }
        else {
            emc_status ( "info",
"Using default values for remote_rdf_dirs for array type ($emcfg{array_type}): $default_rdf_ports{$emcfg{array_type}}"
            );
            $emcfg{remote_rdf_dirs} = $default_rdf_ports{ $emcfg{array_type} };
        }
    }

    ## Figure out the rdf name we want to use as $emcfg{symrdfg}
    if ( !defined $emcfg{symrdfg} ) { emc_set_rdfg_name; }
    if ( $emcfg{symrdfg} eq "NONE" ) { bailout ( 10, "RDF group returned NONE for $emcopts{name}" ); }

    ## In case it's not in use  lets see what our root name is.. e.g. cs99
    my $basename = $emcopts{name};
    $basename =~ s/-.*$//;    ## Remove everything after the dash (e.g. cs99-db becomes cs99)

    ## Lets see if this name is in use already
    foreach my $rdfnum ( sort keys %rdf_info ) {
        if ( $rdf_info{$rdfnum} eq $emcfg{symrdfg} ) { $name_inuse++; $perm_rdfnum = $rdfnum; }
    }

    ## See if we can match our basename to find a range
    if ( !$name_inuse ) {
        ## Loop through ranges 10-60 looking for possible matches
        for ( my $thisrange = 10; $thisrange <= 60; $thisrange = $thisrange + 10 ) {
            if ( defined $rdf_info{$thisrange} ) {
                ## Found a range in use
                if ( $open_range == $thisrange ) {
                    $open_range = $open_range + 10;
                }    ## this range taken if we don't match basename

                ## See if the basename matches
                my $checkbase = $rdf_info{$thisrange};
                if ( $checkbase =~ /^$basename/ ) {
                    ## Found our range
                    $matched_base++;
                    ## Lets find an open group in our range
                    my $lastfound = $thisrange;
                    for ( my $loop = $thisrange; $loop < ( $thisrange + 9 ); $loop++ ) {
                        if ( defined $rdf_info{$loop} ) { $lastfound = $loop; }
                    }
                    ## Using 1 higher than the last open spot we found
                    $perm_rdfnum = $lastfound + 1;
                }
            }
        }
    }

    ## If we didn't match our basename, we're going to use the next open range
    if ( !$perm_rdfnum ) { $perm_rdfnum = $open_range; }

    ## If we are going to use the latest option -format, while doing createpair
    if ( $emcopts{format} ) { $formatOption = "-format"; }

    ## If our name was already in use, we need to use the consistency exempt procedure
    if ($name_inuse) {

        ## Find a temporary group open
        my $tmpgrp = 0;
        for my $key ( sort keys %tmp_rdfgs ) {
            if ( ( !$tmpgrp ) && ( !defined $rdf_info{$key} ) ) { $tmpgrp = $key; }
        }
        if ( !$tmpgrp ) { bailout ( 11, "Unable to find suitable RDF group for consistency exempt procedure." ); }

        ## Create the temporary group
        $exec_srdf{1}{cmd} =
"symrdf -sid $emcfg{sid} -label $tmp_rdfgs{$tmpgrp} -rdfg $tmpgrp -dir $emcfg{local_rdf_dirs} -remote_rdfg $tmpgrp -remote_dir $emcfg{remote_rdf_dirs} -remote_sid $emcfg{array_pair} addgrp -nop";
        $exec_srdf{1}{desc} = "Creating temporary group $tmp_rdfgs{$tmpgrp} ($tmpgrp)";
        $exec_srdf{1}{err}  = "SRDF unable to create temporary group $tmpgrp ($tmp_rdfgs{$tmpgrp})";
        ## Performs a createpair using the pairfile / temporary group
        $exec_srdf{2}{cmd} =
"symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} -type R1 -establish -rdf_mode acp_disk createpair $formatOption -nop";
        $exec_srdf{2}{desc} = "Performing createpair on $tmp_rdfgs{$tmpgrp} ($tmpgrp) using file $emcopts{pairfile}";
        $exec_srdf{2}{err}  = "SRDF unable to perform createpair on temporary group.";
        ## Waits to verify all the devices are synchronized, checks every 10min for just over 2 days
        $exec_srdf{3}{cmd} =
          "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} verify -synchronized -i 600 -c 300";
        $exec_srdf{3}{desc} = "Verifying all devices are synchronized, Trying every 10min.";
        $exec_srdf{3}{err} = "SRDF unable to verify devices in $tmpgrp are synchronized, giving up after 300 attempts.";
        my $processRestSteps=1; #Whether we should process rest of steps or not, we wont in case of secondary & 3dc
        if ( !$emcfg{primary} && $emcopts{'3dc'}) {
            ## If this setup is for R21->R22 (DR side on 4 array setup)
            ## We assume that PriDB to DRDB replication is setup and symdg work is done
            emc_set_symdg_name unless defined $emcfg{symdg};
            print "3ds on secondary side $emcfg{symrdfg} \n";
            #Lets figure out the symdg name of SRDF R1->R2 replication.
            my @LIST = split (/-/, $emcfg{symrdfg});
            my $funcName = $LIST[1]; #Should be either dgdb or dgarch
            my $mainDgName='';
            if ($funcName eq "dgdb") { $mainDgName=$LIST[0]."-dgs";
            } elsif ($funcName eq "dgarch") { $mainDgName=$LIST[0]."-arch-dgs"; }
            #Lets find the rdfg number of the main replication
            my $mainRDFG=0;
            foreach my $rdfnum ( sort keys %rdf_info ) {
                if ( $mainDgName =~ /$rdf_info{$rdfnum}/) { $mainRDFG=$rdfnum; }
            }
            if (( !$mainDgName ) || ( $mainRDFG == 0 )) {
                print "Unable to determine Primary to DR replication name or rdfg group \n";
                print "Wont be able to proceed with automated replication setup for R21->R22 \n";
            }else{
                ## We have got everything we need to proceed, lets move ahead
                $processRestSteps=0;
                ## First lets create our total device file, we need this to chg mode of Permanent group
                ## after moving the new devs
                my $tmpPairFile="./".$mainDgName."_".$perm_rdfnum."_all_devs.out";
                my $filehandle;
                open $filehandle, ">", "$tmpPairFile" or bailout ( 41, "Unable to create file ($tmpPairFile) : $!" );
                my @symrdfgOut = safesymcli ( 0, "symrdf -g $mainDgName -rdfg $perm_rdfnum query" );
                my ($stddev, $clndev);
                #Write the pairs from the permanent group
                foreach (@symrdfgOut) {
                   #Match for
                   #7266105  06105 RW       0       0 RW 06105 WD       0       0 A... Consistent
                   if (/\w{7}\s+(\w{4,5})\s\w+\s+\d+\s+\d+\s+\w+\s+(\w{4,5})/) {
                        $stddev    = substr($1, -4);
                        $clndev    = substr($2, -4);
                        print $filehandle "$stddev $clndev \n";
                   }
                }
                #Now append the new devs to it as well
                open ( ReadHandle, "<", $emcopts{pairfile} ) or bailout ( 400, "Unable to open config file $emcopts{pairfile} :$!" );
                while (<ReadHandle>) { if ($_ !~ /^#/) { print $filehandle $_; } }
                close $filehandle;
                close (ReadHandle);

                ## Ensure Main R1->R2 group is in async/consistent mode
                $exec_srdf{6}{cmd}  = "symrdf -g $mainDgName -rdfg $mainRDFG verify -consistent";
                $exec_srdf{6}{desc} = "Verifying devices in main R1->R2 group $mainDgName are consistent.";
                $exec_srdf{6}{err}  = "SRDF unable to verify main group $mainDgName, $mainRDFG is consistent.";
                ## Now split Main R1->R2 group
                $exec_srdf{7}{cmd}  = "symrdf -g $mainDgName -rdfg $mainRDFG split -nop";
                $exec_srdf{7}{desc} = "Splitting devices in main R1->R2 group $mainDgName.";
                $exec_srdf{7}{err}  = "SRDF unable to split main group $mainDgName, $mainRDFG.";
                ## Now change Main R1->R2 group mode to acp_disk
                $exec_srdf{8}{cmd}  = "symrdf -g $mainDgName -rdfg $mainRDFG set mode acp_disk -nop";
                $exec_srdf{8}{desc} = "Setting main R1->R2 group $mainDgName to acp_disk mode.";
                $exec_srdf{8}{err}  = "SRDF unable to set main group $mainDgName, $mainRDFG to acp_disk mode.";
                ## Sets the temporary group to async mode
                $exec_srdf{9}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} set mode async -nop";
                $exec_srdf{9}{desc} = "Setting $tmp_rdfgs{$tmpgrp} to async.";
                $exec_srdf{9}{err}  = "SRDF unable to set temporary group to async.";
                ## Verifies all the devices get to consistent .. Waits up to 10min
                $exec_srdf{10}{cmd} =
                  "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} verify -consistent -i 60 -c 10";
                $exec_srdf{10}{desc} = "Verifying devices in $tmp_rdfgs{$tmpgrp} are consistent.";
                $exec_srdf{10}{err}  = "SRDF unable to verify devices in $tmpgrp are consistent, giving up after 10min.";
                ## Split the temporary group
                $exec_srdf{11}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} split -nop";
                $exec_srdf{11}{desc} = "Splitting group $tmp_rdfgs{$tmpgrp} .";
                $exec_srdf{11}{err}  = "SRDF unable to split temporary group.";
                ## Change the Permanent group to async mode
                $exec_srdf{12}{cmd}  = "symrdf -g $mainDgName -rdfg $perm_rdfnum set mode async -nop";
                $exec_srdf{12}{desc} = "Changing devices in permanent group $mainDgName, $perm_rdfnum to async mode.";
                $exec_srdf{12}{err}  = "SRDF unable to change permanent group $mainDgName, $perm_rdfnum to async mode.";
                ## Move devs from temporary group to permanent group
                $exec_srdf{13}{cmd} =
"symrdf -sid $emcfg{sid} -rdfg $tmpgrp -new_rdfg $perm_rdfnum -file $emcopts{pairfile} -cons_exempt movepair -nop";
                $exec_srdf{13}{desc} = "Moving devices from $tmp_rdfgs{$tmpgrp} to permanent group $emcfg{symrdfg}.";
                $exec_srdf{13}{err} =
                  "SRDF unable to move devices from temporary group ($tmpgrp) to permanent group ($perm_rdfnum).";
                ## Modify the mode of permanent group from async back to acp_disk
                $exec_srdf{14}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $tmpPairFile set mode acp_disk -nop";
                $exec_srdf{14}{desc} = "Changing devices in permanent group $mainDgName, $perm_rdfnum to acp_disk mode.";
                $exec_srdf{14}{err}  = "SRDF unable to change permanent group $mainDgName, $perm_rdfnum to acp_disk mode.";
                ## Now change Main R1->R2 group mode back to async
                $exec_srdf{15}{cmd}  = "symrdf -g $mainDgName -rdfg $mainRDFG set mode async -nop";
                $exec_srdf{15}{desc} = "Setting main R1->R2 group $mainDgName to async mode.";
                $exec_srdf{15}{err}  = "SRDF unable to set main group $mainDgName, $mainRDFG to async mode.";
                ## Now resume back the Main R1->R2 replication
                $exec_srdf{16}{cmd}  = "symrdf -g $mainDgName -rdfg $mainRDFG establish -nop";
                $exec_srdf{16}{desc} = "Establishing/resuming devices in main R1->R2 group $mainDgName, $mainRDFG";
                $exec_srdf{16}{err}  = "SRDF unable to establish (resume) main group $mainDgName, $mainRDFG.";
                ## Remove the temporary group
                $exec_srdf{17}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $tmpgrp removegrp -nop";
                $exec_srdf{17}{desc} = "Removing temporary group $tmp_rdfgs{$tmpgrp}.";
                $exec_srdf{17}{err}  = "SRDF unable to cleanup temporary group ($tmpgrp).";
            }
        }
        if ($processRestSteps) {
            ## Sets the temporary group to async mode
            $exec_srdf{4}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} set mode async -nop";
            $exec_srdf{4}{desc} = "Setting $tmp_rdfgs{$tmpgrp} to async.";
            $exec_srdf{4}{err}  = "SRDF unable to set temporary group to async.";
            ## Verifies all the devices get to consistent .. Waits up to 10min
            $exec_srdf{5}{cmd} =
              "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} verify -consistent -i 60 -c 10";
            $exec_srdf{5}{desc} = "Verifying devices in $tmp_rdfgs{$tmpgrp} are consistent.";
            $exec_srdf{5}{err}  = "SRDF unable to verify devices in $tmpgrp are consistent, giving up after 10min.";
            ## Suspends the temporary group
            $exec_srdf{6}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $tmpgrp -file $emcopts{pairfile} suspend -nop";
            $exec_srdf{6}{desc} = "Suspending group $tmp_rdfgs{$tmpgrp} .";
            $exec_srdf{6}{err}  = "SRDF unable to suspend temporary group.";
            ## Ensure Permanent group is in async mode
            emc_set_symdg_name unless defined $emcfg{symdg};
            $exec_srdf{7}{cmd}  = "symrdf -g $emcfg{symdg} verify -consistent";
            $exec_srdf{7}{desc} = "Verifying devices in permanent group $emcfg{symrdfg} are consistent.";
            $exec_srdf{7}{err}  = "SRDF unable to verify permanent group $perm_rdfnum is consistent.";
            ## Move devs from temporary group to permanent group
            $exec_srdf{8}{cmd} =
"symrdf -sid $emcfg{sid} -rdfg $tmpgrp -new_rdfg $perm_rdfnum -file $emcopts{pairfile} -cons_exempt movepair -nop";
            $exec_srdf{8}{desc} = "Moving devices from $tmp_rdfgs{$tmpgrp} to permanent group $emcfg{symrdfg}.";
            $exec_srdf{8}{err} =
              "SRDF unable to move devices from temporary group ($tmpgrp) to permanent group ($perm_rdfnum).";
            ## Resume permanent group
            $exec_srdf{9}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $emcopts{pairfile} resume -nop";
            $exec_srdf{9}{desc} = "Resuming devices in permanent group $emcfg{symrdfg}.";
            $exec_srdf{9}{err}  = "SRDF unable to resume permanent group ($perm_rdfnum)";
            ## Ensure permanent group is all back in async mode we will wait up to 10min
            $exec_srdf{10}{cmd} =
              "symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $emcopts{pairfile} verify -consistent -i 60 -c 10";
            $exec_srdf{10}{desc} = "Ensuring permanent group is consistent $emcfg{symrdfg}.";
            $exec_srdf{10}{err} =
              "SRDF unable to verify permanent group $perm_rdfnum is consistent. Giving up after 10min.";
            ## Remove the temporary group
            $exec_srdf{11}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $tmpgrp removegrp -nop";
            $exec_srdf{11}{desc} = "Removing temporary group $tmp_rdfgs{$tmpgrp}.";
            $exec_srdf{11}{err}  = "SRDF unable to cleanup temporary group ($tmpgrp).";
        }
    }

    ## If our name wasn't in use we don't need to use the consistency exempt procedure
    else {
        ## Creates our group
        $exec_srdf{1}{cmd} =
"symrdf -sid $emcfg{sid} -label $emcfg{symrdfg} -rdfg $perm_rdfnum -dir $emcfg{local_rdf_dirs} -remote_rdfg $perm_rdfnum -remote_dir $emcfg{remote_rdf_dirs} -remote_sid $emcfg{array_pair} addgrp -nop";
        $exec_srdf{1}{desc} = "Creating RDF group $emcfg{symrdfg} ($perm_rdfnum)";
        $exec_srdf{1}{err}  = "SRDF unable to create group $perm_rdfnum ($emcfg{symrdfg}).";
        ## Performs a createpair using the pairfile
        $exec_srdf{2}{cmd} =
"symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $emcopts{pairfile} -type R1 -establish -rdf_mode acp_disk createpair $formatOption -nop";
        $exec_srdf{2}{desc} = "Performing createpair on $emcfg{symrdfg} using file $emcopts{pairfile}";
        $exec_srdf{2}{err}  = "SRDF unable to perform createpair on group $perm_rdfnum.";
        ## Waits to verify all the devices are synchronized, checks every 10min for just over 2 days
        $exec_srdf{3}{cmd} =
          "symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $emcopts{pairfile} verify -synchronized -i 600 -c 300";
        $exec_srdf{3}{desc} = "Verifying all devices are synchronized, Trying every 10min.";
        $exec_srdf{3}{err} =
          "SRDF unable to verify devices in group $perm_rdfnum are synchronized, giving up after 300 attempts.";
        ## Sets the group to async mode
        $exec_srdf{4}{cmd}  = "symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $emcopts{pairfile} set mode async -nop";
        $exec_srdf{4}{desc} = "Setting $emcfg{symrdfg} to async.";
        $exec_srdf{4}{err}  = "SRDF unable to set group $perm_rdfnum to async.";
        ## Verifies all the devices get to synchronized .. Waits up to 1hr
        $exec_srdf{5}{cmd} =
          "symrdf -sid $emcfg{sid} -rdfg $perm_rdfnum -file $emcopts{pairfile} verify -consistent -i 60 -c 10";
        $exec_srdf{5}{desc} = "Verifying all devices are consistent, Trying every 1min.";
        $exec_srdf{5}{err}  = "SRDF unable to verify devices in $perm_rdfnum are consistent, giving up after 10min.";
    }

    ## Run the srdf commands
    if ( defined $exec_srdf{1}{cmd} ) { emc_exec_srdf_cmds; }

}

###########################################
## DMX Subroutines - May call other subs ##
###########################################
sub emc_run_dmx_map {
    ## Maps metas for DMX platform
    my @mapcmds    = ();    ## Stores the mapping commands
    my $mapped_yet = 0;     ## Tracks if we actually mapped anything

    emc_fa_used;            ## Gathers used FA ports and stores them in %fa_mapping

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_map_20120201_999
    $emcfg{mapfile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_map_" . shortdate . "_$emcfg{sessionid}";

    ## Human Header ##
    @mapcmds =
      ( @mapcmds, symconfigure_human_header ( $emcfg{mapfile} ) );  ## Adds the human header to our current output array

    ### Constarnation Header ##
    push ( @mapcmds, "##Constarnation:CMD:353:$SYMCLI/symconfigure -sid $emcfg{sid} -f $emcfg{mapfile} commit -nop" );
    push ( @mapcmds, "##Constarnation:MUST:The configuration change session has successfully completed" );
    push ( @mapcmds, "##Constarnation:NEVER:The configuration change session has failed" );

    foreach my $thisfa ( sort keys %lun_mapping ) {
        push ( @mapcmds, "## FA-$thisfa ##" );    ## separator lines in the output to make it look better
        foreach my $thisdev ( sort keys %{ $lun_mapping{$thisfa} } ) {
            ## This gives us lun_mapping{$thisfa}{$thisdev} = 1 right now
            my $thisscsi = emc_get_next_fa_avail ($thisfa);
            $mapped_yet++;                        ## Tracks that we mapped something
            push ( @mapcmds, "map dev $thisdev to dir $thisfa target=0 lun=$thisscsi" . ";" );
            $fa_mapping{$thisfa}{$thisscsi} = 1;    ## Sets this SCSID in use so we don't grab it again
        }
    }

    ## Create our Map File
    if ($mapped_yet) { create_output_file ( $emcfg{mapfile}, $emcfg{user_uid}, @mapcmds ); }
    else             { emc_status ( "warn", "Did not map anything, not writing file" ); undef $emcfg{mapfile}; }
}

sub emc_run_alias {
    ## Creates aliases
    ## Uses host_hba key from %host_mapping to ensure we only have unique entries
    ## Then we pull the WWN from %wwnnames to create the alias
    ## called by emc_main
    my @aliascmds     = ();    ## Stores alias commands
    my $created_alias = 0;     ## Tracks if we created any aliases

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_awwn_20120201_999.sh
    $emcfg{aliasfile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_awwn_" . shortdate . "_$emcfg{sessionid}" . ".sh";

    ## Human Header ##
    push ( @aliascmds, "## Execute this file as shell script : 'sudo ./$emcfg{aliasfile}'" );
    push ( @aliascmds, "## " . logtime . " Created automatically via $0" );
    push ( @aliascmds, "##" );

    ## Constarnation Header .. No need for MUST, can exit quietly
    push ( @aliascmds, "##Constarnation:CMD:753:./$emcfg{aliasfile}" );
    push ( @aliascmds, "##Constarnation:NEVER:Invalid" );

    ## Create the Aliases
    foreach my $this_host_hba ( sort keys %host_mapping ) {
        my $this_host_alias = $this_host_hba;
        $this_host_alias =~ s/_/\//;    ## Replace the _hba with /hba for symmask

        ## Aliases can't be super long, so let's shorten what we can
        $this_host_alias =~ s/ops-//;          ## strip out ops in the name
        $this_host_alias =~ s/shared-//;       ## strip out shared- from nfs hosts
        $this_host_alias =~ s/indexer/idx/;    ## swap indexer with idx
        $this_host_alias =~ s/csearch/cdx/;    ## swap csearch with idx

        ## If this hba has a WWN lets push the alias
        if ( defined $wwnnames{$this_host_hba} ) {
            if ( $emcfg{array_type} =~ /DMX/ ) {
                $created_alias++;
                push ( @aliascmds,
                    "$SYMCLI/symmask -sid $emcfg{sid} -wwn $wwnnames{$this_host_hba} rename $this_host_alias" );
            }
            elsif ( $emcfg{array_type} =~ /VMAX/ ) {
                $created_alias++;
                push ( @aliascmds,
                    "$SYMCLI/symaccess -sid $emcfg{sid} -wwn $wwnnames{$this_host_hba} rename -alias $this_host_alias"
                );
            }
        }
    }

    ## Create our Alias File
    if ($created_alias) { create_output_file ( $emcfg{aliasfile}, $emcfg{user_uid}, @aliascmds ); }
    else { emc_status ( "warn", "Did not find any aliases to create. Not writing file" ); undef $emcfg{aliasfile}; }
}

sub emc_run_alias_dg {
    ## Creates aliases for DG array
    ## Uses host_hba key from %dghost_mapping to ensure we only have unique entries
    ## Then we pull the WWN from %dgwwnnames to create the alias
    ## called by emc_main
    my @dgaliascmds     = ();    ## Stores alias commands
    my $created_alias = 0;     ## Tracks if we created any aliases

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_awwn_20120201_999.sh
    $emcfg{dgaliasfile} = "$emcfg{sfdc}" . "_$emcopts{dgname}" . "_awwn_" . shortdate . "_$emcfg{sessionid}" . ".sh";

    ## Human Header ##
    push ( @dgaliascmds, "## Execute this file as shell script : 'sudo ./$emcfg{dgaliasfile}'" );
    push ( @dgaliascmds, "## " . logtime . " Created automatically via $0" );
    push ( @dgaliascmds, "##" );

    ## Constarnation Header .. No need for MUST, can exit quietly
    push ( @dgaliascmds, "##Constarnation:CMD:783:./$emcfg{dgaliasfile}" );
    push ( @dgaliascmds, "##Constarnation:NEVER:Invalid" );

    ## Create the Aliases
    foreach my $this_host_hba ( sort keys %dghost_mapping ) {
        my $this_host_alias = $this_host_hba;
        $this_host_alias =~ s/_/\//;    ## Replace the _hba with /hba for symmask

        ## Aliases can't be super long, so let's shorten what we can
        $this_host_alias =~ s/ops-//;          ## strip out ops in the name
        $this_host_alias =~ s/shared-//;       ## strip out shared- from nfs hosts
        $this_host_alias =~ s/indexer/idx/;    ## swap indexer with idx
        $this_host_alias =~ s/csearch/cdx/;    ## swap csearch with idx

        ## If this hba has a WWN lets push the alias
        if ( defined $dgwwnnames{$this_host_hba} ) {
            if ( $emcfg{partner_array_type} =~ /VMAX/ ) {
                $created_alias++;
                push ( @dgaliascmds,
                    "$SYMCLI/symaccess -sid $emcfg{partner_sid} -wwn $dgwwnnames{$this_host_hba} rename -alias $this_host_alias"
                );
            }
        }
    }

    ## Create our Alias File
    if ($created_alias) { create_output_file ( $emcfg{dgaliasfile}, $emcfg{user_uid}, @dgaliascmds ); }
    else { emc_status ( "warn", "Did not find any aliases to create. Not writing file" ); undef $emcfg{dgaliasfile}; }
}

sub emc_run_dmx_mask {
    ## Masks individual files for DMX platform
    my @maskcmds     = ();    ## Stores masking commands
    my $created_mask = 0;     ## Tracks if we masked anything

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_mask_20120201_999.sh
    $emcfg{maskfile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_mask_" . shortdate . "_$emcfg{sessionid}" . ".sh";

    ## Human Header ##
    push ( @maskcmds, "## Execute this file as shell script : 'sudo ./$emcfg{maskfile}'" );
    push ( @maskcmds, "## " . logtime . " Created automatically via $0" );
    push ( @maskcmds, "##" );

    ## Constarnation Header .. symmask won't provide any usable output, depending on emcmask.pl or symmask to provide it
    push ( @maskcmds, "##Constarnation:CMD:553:./$emcfg{maskfile}" );
    push ( @maskcmds, "##Constarnation:NEVER:try again" );
    push ( @maskcmds, "##Constarnation:NEVER:Error while executing command" );

    ## Need to reformat the wwn for emcmask.pl, so lets do that now
    my $emcmask_sid = $emcfg{sid};
    $emcmask_sid =~ s/^000//;

    ## Backup masking header
    push ( @maskcmds, "echo \"Backing up masking database for $emcfg{sid} ...\"" );
    push ( @maskcmds, "/usr/local/bin/emcmask.pl -s $emcmask_sid -a backup" );

    ## Create masking lines
    foreach my $this_host_hba ( sort keys %host_mapping ) {
        my $this_host_alias = $this_host_hba;

        ## Run through %host_mapping looking for FA's
        foreach my $thisfa ( sort keys %{ $host_mapping{$this_host_hba} } ) {
            my $thisfa_name = $thisfa;    ## e.g. 3a:1
            my $thisfa_port = $thisfa;
            $thisfa_name =~ s/:\d$//;                    ## Removes ":1"
            $thisfa_port =~ s/^[0-9]{1,2}[A-Ha-h]://;    ## Removes "3a:"

            ## Make sure we have devices listed for this FA
            my $devlist  = "";                           ## Holds our devices for this FA
            my $foundevs = 0;                            ## Tracks if this FA has any devs to mask
            foreach my $thisdev ( sort keys %{ $lun_mapping{$thisfa} } ) {
                if ( !$foundevs ) { $foundevs++; $devlist = $thisdev; }
                else              { $devlist = $devlist . ",$thisdev"; }
            }
            ## If we found some devices we'll mask them now
            if ($foundevs) {

                ## Going to mask by WWN only, we'll set aliases later
                ## If we are doing aliases we'll mask via alias, otherwise we'll do wwns
#if (defined $emcopts{alias}) {
#       $created_mask++;
#       $this_host_alias =~ s/_/\//;
#       push(@maskcmds,"echo \"Masking AWWN-$this_host_alias FA-$thisfa DEVS-($devlist)\"");
#       push(@maskcmds,"$SYMCLI/symmask -sid $emcfg{sid} -awwn $this_host_alias -dir $thisfa_name -p $thisfa_port add devs $devlist -nop");
#       }
                ## Didn't request aliases, so we'll do WWNs
                #elsif (defined $wwnnames{$this_host_hba}) {
                if ( defined $wwnnames{$this_host_hba} ) {
                    $created_mask++;
                    push ( @maskcmds,
                        "echo \"Masking WWN-$wwnnames{$this_host_hba} ($this_host_hba) FA-$thisfa DEVS-($devlist)\"" );
                    push ( @maskcmds,
"$SYMCLI/symmask -sid $emcfg{sid} -wwn $wwnnames{$this_host_hba} -dir $thisfa_name -p $thisfa_port add devs $devlist -nop"
                    );
                }
                ## Unable to determine WWN sorry, gotta skip
                else { emc_status ( "warn", "Unable to determine WWN for $this_host_hba , not masking." ); }
            }
        }
    }

    ## Masking refresh footer
    push ( @maskcmds, "echo \"Refreshing masking database for $emcfg{sid} ...\"" );
    push ( @maskcmds, "$SYMCLI/symmask -sid $emcfg{sid} refresh -nop" );

    ## Create our Masking File
    if ($created_mask) { create_output_file ( $emcfg{maskfile}, $emcfg{user_uid}, @maskcmds ); }
    else { emc_status ( "warn", "Did not find any devices to mask. Not writing file" ); undef $emcfg{maskfile}; }
}

############################################
## VMAX subroutines - May call other subs ##
############################################
sub emc_get_existing_auto {
    ## Gathers existing auto provisioning groups
    ## Stores views in $exist_views
    ## Stores Initiator Groups, Port Groups, and Storage groups in %exist_ig  %exist_pg and %exist_sg

    my ($arrayserial) = @_;

    ## Run symaccess -sid XXX list and parse the output
    my @output = safesymcli ( 0, "symaccess -sid $arrayserial list" );
    foreach (@output) {
        ## Initiator Lines
        if (/^(\S*)\s*Initiator$/) {
            if ( !defined $exist_ig{$1} ) { $exist_ig{$1} = 1; }
        }
        ## Initiator Lines
        if (/^(\S*)\s*Port$/) {
            if ( !defined $exist_pg{$1} ) { $exist_pg{$1} = 1; }
        }
        ## Storage Lines
        if (/^(\S*)\s*Storage$/) {
            if ( !defined $exist_pg{$1} ) { $exist_sg{$1} = 1; }
        }
    }

    ## Gather Views
    my @view_output = safesymcli ( 0, "symaccess -sid $arrayserial list view -v" );
    foreach (@view_output) {
        if (/^Masking View Name\s*:\s(\w*)/) {
            if ( !defined $exist_view{$1} ) { $exist_view{$1} = 1; }
        }
    }
}

sub emc_create_ig {
    ## Creates initiator groups. Returns a list of the commands it wants to run
    my @igcmds   = ();    ## Holds IG commands

    ## Header - 1st Level initiator groups
    push ( @igcmds, "##" );
    push ( @igcmds, "## Initiator Groups" );
    push ( @igcmds, "##" );
    push ( @igcmds, "## First Level Initiator Groups" );
    push ( @igcmds, "echo \"## Creating First Level Initiator Groups\"" );

    ## Creates 1st level initiator groups, these are host_hba => WWN
    foreach my $host_hba ( sort keys %wwnnames ) {

        ## Create the HOST_HBA_IG if it doesn't exist yet
        if ( !defined $exist_ig{ $host_hba . "_ig" } ) {
            push ( @igcmds,
                    "$SYMCLI/symaccess -sid $emcfg{sid} create -type initiator -name $host_hba"
                  . "_ig -wwn $wwnnames{$host_hba}" );
            ## Flag them as created so we don't do it again
            $exist_ig{ $host_hba . "_ig" } = 1;
        }
    }

    ## Header - Cascade initiator groupss
    push ( @igcmds, "## Cascade Initiator Groups" );
    push ( @igcmds, "echo \"## Creating Cascade Initiator Groups\"" );

    ## Create our Cascade initiator groups  e.g. cs99-db-3e1-10e1_ig
    my $this_fa_partner;
    my $max_fa_number;
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                       $this_fa_partner = fapartner_r5 ($this_fa);
                       $max_fa_number=2;
                } else {
                       $this_fa_partner = fapartner ($this_fa);
                       $max_fa_number=8;
         }

        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only want to operate on the lower half, so the format remains the same
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            $formatted_fa =~ s/://;        ## Removes the ugly colon
            my $formatted_partner;
            if ( $emcfg{array_type} eq "VMAX100K" ||  $emcfg{array_type} eq "VMAX200K" ) {
               $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
               $formatted_partner = fapartner ($formatted_fa);
            }

            ## Create the cascade group
            my $this_cascade = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_ig";
            if ( !defined $exist_ig{$this_cascade} ) {
                push ( @igcmds, "$SYMCLI/symaccess -sid $emcfg{sid} create -type initiator -name $this_cascade" );
                $exist_ig{$this_cascade} = 1;

                ## Fill the Cascade
                foreach my $host_hba ( sort keys %host_mapping ) {
                    foreach my $mapping_fa ( sort keys %{ $host_mapping{$host_hba} } ) {
                        if ( ( $mapping_fa eq $this_fa ) || ( $mapping_fa eq $this_fa_partner ) ) {
                            push ( @igcmds,
" $SYMCLI/symaccess -sid  $emcfg{sid} -type initiator -name $this_cascade add -ig $host_hba"
                                  . "_ig" );
                        }
                    }
                }
            }
        }
    }
    return (@igcmds);
}

sub emc_create_ig_dg {
    ## For DG array, creates initiator groups. Returns a list of the commands it wants to run
    my @dgigcmds   = ();    ## Holds IG commands

    ## Header - 1st Level initiator groups
    push ( @dgigcmds, "##" );
    push ( @dgigcmds, "## Initiator Groups" );
    push ( @dgigcmds, "##" );
    push ( @dgigcmds, "## First Level Initiator Groups" );
    push ( @dgigcmds, "echo \"## Creating First Level Initiator Groups\"" );

    ## Creates 1st level initiator groups, these are host_hba => WWN
    foreach my $host_hba ( sort keys %dgwwnnames ) {

        ## Create the HOST_HBA_IG if it doesn't exist yet
        if ( !defined $exist_ig{ $host_hba . "_ig" } ) {
            push ( @dgigcmds,
                    "$SYMCLI/symaccess -sid $emcfg{partner_sid} create -type initiator -name $host_hba"
                  . "_ig -wwn $dgwwnnames{$host_hba}" );
            ## Flag them as created so we don't do it again
            $exist_ig{ $host_hba . "_ig" } = 1;
        }
    }

    ## Header - Cascade initiator groupss
    push ( @dgigcmds, "## Cascade Initiator Groups" );
    push ( @dgigcmds, "echo \"## Creating Cascade Initiator Groups\"" );

    ## Create our Cascade initiator groups  e.g. cs99-db-3e1-10e1_ig
    my $this_fa_partner;
    my $max_fa_number;
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
                       $this_fa_partner = fapartner_r5 ($this_fa);
                       $max_fa_number=2;
                } else {
                       $this_fa_partner = fapartner ($this_fa);
                       $max_fa_number=8;
         }

        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only want to operate on the lower half, so the format remains the same
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            $formatted_fa =~ s/://;        ## Removes the ugly colon
            my $formatted_partner;
            if ( $emcfg{partner_array_type} eq "VMAX100K" ||  $emcfg{partner_array_type} eq "VMAX200K" ) {
               $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
               $formatted_partner = fapartner ($formatted_fa);
            }

            ## Create the cascade group
            my $this_cascade = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_ig";
            if ( !defined $exist_ig{$this_cascade} ) {
                push ( @dgigcmds, "$SYMCLI/symaccess -sid $emcfg{partner_sid} create -type initiator -name $this_cascade" );
                $exist_ig{$this_cascade} = 1;

                ## Fill the Cascade
                foreach my $host_hba ( sort keys %dghost_mapping ) {
                    foreach my $mapping_fa ( sort keys %{ $dghost_mapping{$host_hba} } ) {
                        if ( ( $mapping_fa eq $this_fa ) || ( $mapping_fa eq $this_fa_partner ) ) {
                            push ( @dgigcmds,
" $SYMCLI/symaccess -sid  $emcfg{partner_sid} -type initiator -name $this_cascade add -ig $host_hba"
                                  . "_ig" );
                        }
                    }
                }
            }
        }
    }
    return (@dgigcmds);
}

sub emc_create_pg {
    ## Create Port groups
    my @pgcmds = ();    ## Port Group commands returned

    ## Human Header
    push ( @pgcmds, "##" );
    push ( @pgcmds, "## Port Groups" );
    push ( @pgcmds, "##" );
    push ( @pgcmds, "echo \"## Creating Port Groups\"" );

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number;
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                       $this_fa_partner = fapartner_r5 ($this_fa);
                       $max_fa_number=2;
                } else {
                       $this_fa_partner = fapartner ($this_fa);
                       $max_fa_number=8;
         }
        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            $formatted_fa =~ s/://;        ## Removes the ugly colon
            my $formatted_partner;
            if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
               $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
               $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_pg = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_pg";

            ## Create Port Group if it doesn't exist already
            if ( !defined $exist_pg{$this_pg} ) {
                push ( @pgcmds,
"$SYMCLI/symaccess -sid $emcfg{sid} create -type port -name $this_pg -dirport $this_fa,$this_fa_partner"
                );

                ## Save this port group so we don't create it again
                $exist_pg{$this_pg} = 1;
            }
        }
    }
    return (@pgcmds);
}

sub emc_create_pg_dg {
    ## Create Port groups for DG array
    my @dgpgcmds = ();    ## Port Group commands returned

    ## Human Header
    push ( @dgpgcmds, "##" );
    push ( @dgpgcmds, "## Port Groups" );
    push ( @dgpgcmds, "##" );
    push ( @dgpgcmds, "echo \"## Creating Port Groups\"" );

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number;
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
                       $this_fa_partner = fapartner_r5 ($this_fa);
                       $max_fa_number=2;
                } else {
                       $this_fa_partner = fapartner ($this_fa);
                       $max_fa_number=8;
         }
        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            $formatted_fa =~ s/://;        ## Removes the ugly colon
            my $formatted_partner;
            if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
               $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
               $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_pg = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_pg";

            ## Create Port Group if it doesn't exist already
            if ( !defined $exist_pg{$this_pg} ) {
                push ( @dgpgcmds,
"$SYMCLI/symaccess -sid $emcfg{partner_sid} create -type port -name $this_pg -dirport $this_fa,$this_fa_partner"
                );

                ## Save this port group so we don't create it again
                $exist_pg{$this_pg} = 1;
            }
        }
    }
    return (@dgpgcmds);
}

sub emc_create_sg {
    ## Creates Storage groups
    my @sgcmds     = ();    ## Storage group commands
    my @dgsgcmds   = ();    ## Storage group commands for DG Array
    my @boguscmds  = ();    ## Empty array we will send back if we fail to find any storage groups
    my $created_sg = 0;     ## Tracks if we created any storage groups
    my $dgcreated_sg = 0;   ## Tracks if we created any storage groups for DG Array

    ## Human Header
    push ( @sgcmds, "##" );
    push ( @sgcmds, "## Storage Groups" );
    push ( @sgcmds, "##" );
    push ( @sgcmds, "echo \"## Creating Storage Groups\"" );

    push ( @dgsgcmds, "##" );
    push ( @dgsgcmds, "## Storage Groups" );
    push ( @dgsgcmds, "##" );
    push ( @dgsgcmds, "echo \"## Creating Storage Groups\"" );

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number; # 8 for vmax2 and 2 for vmax3
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                      $this_fa_partner = fapartner_r5 ($this_fa);
                      $max_fa_number=2;
               } else {
                      $this_fa_partner = fapartner ($this_fa);
                      $max_fa_number=8;
        }
        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            my $formatted_partner;
            $formatted_fa =~ s/://;        ## Removes the : for the port group name
            if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                 $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
                 $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_sg   = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_sg";

            ## Create Port Group if it doesn't exist already
            if ( !defined $exist_sg{$this_sg} ) {
                my $sg_devlist = 0;        ## Tracks the devs we are going to include in this storage group

                ## Generates our list of devices
                foreach my $thisdev ( sort keys %{ $lun_mapping{$this_fa} } ) {
                    if   ( !$sg_devlist ) { $sg_devlist = "$thisdev"; }
                    else                  { $sg_devlist = $sg_devlist . ",$thisdev"; }
                }

                ## Create The Storage Group
                push ( @sgcmds,
                    "$SYMCLI/symaccess -sid $emcfg{sid} create -type storage -name $this_sg -devs $sg_devlist" );
                $created_sg++;

                ## Save this port group so we don't create it again
                $exist_sg{$this_sg} = 1;
            }
            if ( $emcopts{'3dc'} ) { ## Check SG for DG Array
                my $dgthis_sg = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_sg";
                ## Create Port Group if it doesn't exist already
                if ( !defined $exist_sg{$dgthis_sg} ) {
                    my $sg_devlist = 0;        ## Tracks the devs we are going to include in this storage group

                    ## Generates our list of devices
                    foreach my $thisdev ( sort keys %{ $lun_mapping{$this_fa} } ) {
                        if   ( !$sg_devlist ) { $sg_devlist = "$thisdev"; }
                        else                  { $sg_devlist = $sg_devlist . ",$thisdev"; }
                    }

                    ## Create The Storage Group
                    push ( @dgsgcmds,
                        "$SYMCLI/symaccess -sid $emcfg{partner_sid} create -type storage -name $dgthis_sg -devs $sg_devlist" );
                    $dgcreated_sg++;

                    ## Save this port group so we don't create it again
                    $exist_sg{$dgthis_sg} = 1;
                }
            }
        }
    }
    ## If we didn't find anything return empty array
    if ( ($created_sg) && ($dgcreated_sg) ) {
        return (\@sgcmds, \@dgsgcmds);
    } elsif ( ($created_sg) && (! $dgcreated_sg) ) {
        return (\@sgcmds, \@boguscmds);
    } elsif ( (! $created_sg) && ($dgcreated_sg) ) {
        return (\@boguscmds, \@dgsgcmds);
    } elsif ( (! $created_sg) && (! $dgcreated_sg) ) {
        return (\@boguscmds, \@boguscmds);
    }
}

sub emc_create_view {
    ## Creates views for VMAX auto provisioning
    my @viewcmds = ();

    ## Human Header
    push ( @viewcmds, "##" );
    push ( @viewcmds, "## Views" );
    push ( @viewcmds, "##" );
    push ( @viewcmds, "echo \"## Creating Auto Provisoning Views\"" );

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number; # 8 for vmax2 and 3 for vmax3
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                      $this_fa_partner = fapartner_r5 ($this_fa);
                      $max_fa_number=2;
               } else {
                      $this_fa_partner = fapartner ($this_fa);
                      $max_fa_number=8;
        }
        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            my $formatted_partner;
            $formatted_fa =~ s/://;        ## Removes the : for the port group name
            if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                 $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
                 $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_view         = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_view";
            my $this_ig           = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_ig";
            my $this_pg           = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_pg";
            my $this_sg           = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_sg";

            ## Create Port Group if it doesn't exist already
            if ( !defined $exist_view{$this_view} ) {
                push ( @viewcmds,
"$SYMCLI/symaccess -sid $emcfg{sid} create view -name $this_view -ig $this_ig -pg $this_pg -sg $this_sg"
                );

                ## Save this port group so we don't create it again
                $exist_view{$this_view} = 1;
            }
        }
    }
    return (@viewcmds);
}

sub emc_create_view_dg {
    ## Creates views for VMAX auto provisioning for DG Array
    my @dgviewcmds = ();

    ## Human Header
    push ( @dgviewcmds, "##" );
    push ( @dgviewcmds, "## Views" );
    push ( @dgviewcmds, "##" );
    push ( @dgviewcmds, "echo \"## Creating Auto Provisoning Views\"" );

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number; # 8 for vmax2 and 3 for vmax3
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
                      $this_fa_partner = fapartner_r5 ($this_fa);
                      $max_fa_number=2;
               } else {
                      $this_fa_partner = fapartner ($this_fa);
                      $max_fa_number=8;
        }
        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            my $formatted_partner;
            $formatted_fa =~ s/://;        ## Removes the : for the port group name
            if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
                 $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
                 $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_view         = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_view";
            my $this_ig           = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_ig";
            my $this_pg           = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_pg";
            my $this_sg           = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_sg";

            ## Create Port Group if it doesn't exist already
            if ( !defined $exist_view{$this_view} ) {
                push ( @dgviewcmds,
"$SYMCLI/symaccess -sid $emcfg{partner_sid} create view -name $this_view -ig $this_ig -pg $this_pg -sg $this_sg"
                );

                ## Save this port group so we don't create it again
                $exist_view{$this_view} = 1;
            }
        }
    }
    return (@dgviewcmds);
}

sub emc_add_to_sg {
    ## Adds devices to storage groups
    my @sgaddcmds = ();

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number;
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
                       $this_fa_partner = fapartner_r5 ($this_fa);
                       $max_fa_number=2;
                } else {
                       $this_fa_partner = fapartner ($this_fa);
                       $max_fa_number=8;
         }

        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            $formatted_fa =~ s/://;        ## Removes the ugly colon
            my $formatted_partner;
            if ( $emcfg{array_type} eq "VMAX100K" || $emcfg{array_type} eq "VMAX200K" ) {
               $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
               $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_sg = "$emcopts{name}-$formatted_fa-$formatted_partner" . "_sg";

            ## If the storage group exists we'll add our storage to it
            if ( defined $exist_sg{$this_sg} ) {
                my $sg_devlist = 0;        ## Tracks the devs we are going to include in this storage group

                ## Generates our list of devices
                foreach my $thisdev ( sort keys %{ $lun_mapping{$this_fa} } ) {
                    if   ( !$sg_devlist ) { $sg_devlist = "$thisdev"; }
                    else                  { $sg_devlist = $sg_devlist . ",$thisdev"; }
                }

                ## Add storage to the storage group if we found any devices
                if ($sg_devlist) {
                    push ( @sgaddcmds,
                        "$SYMCLI/symaccess -sid $emcfg{sid} -type storage -name $this_sg add devs $sg_devlist" );
                }
            }
        }
    }
    return @sgaddcmds;
}

sub emc_add_to_sg_dg {
    ## Adds devices to storage groups to DG Array
    my @dgsgaddcmds = ();

    ## Get FA Pairs
    my $this_fa_partner;
    my $max_fa_number;
    foreach my $this_fa ( sort keys %lun_mapping ) {
        if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
                       $this_fa_partner = fapartner_r5 ($this_fa);
                       $max_fa_number=2;
                } else {
                       $this_fa_partner = fapartner ($this_fa);
                       $max_fa_number=8;
         }

        my $fa_base = $this_fa;
        $fa_base =~ s/[A-Ha-h]:[0-9][0-9]{0,1}//;    ## Gives just the FA num

        ## Only operating on lower half so we don't duplicate
        if ( $fa_base <= $max_fa_number ) {
            my $formatted_fa = $this_fa;
            $formatted_fa =~ s/://;        ## Removes the ugly colon
            my $formatted_partner;
            if ( $emcfg{partner_array_type} eq "VMAX100K" || $emcfg{partner_array_type} eq "VMAX200K" ) {
               $formatted_partner = fapartner_r5 ($formatted_fa);
            } else {
               $formatted_partner = fapartner ($formatted_fa);
            }
            my $this_sg = "$emcopts{dgname}-$formatted_fa-$formatted_partner" . "_sg";

            ## If the storage group exists we'll add our storage to it
            if ( defined $exist_sg{$this_sg} ) {
                my $sg_devlist = 0;        ## Tracks the devs we are going to include in this storage group

                ## Generates our list of devices
                foreach my $thisdev ( sort keys %{ $lun_mapping{$this_fa} } ) {
                    if   ( !$sg_devlist ) { $sg_devlist = "$thisdev"; }
                    else                  { $sg_devlist = $sg_devlist . ",$thisdev"; }
                }

                ## Add storage to the storage group if we found any devices
                if ($sg_devlist) {
                    push ( @dgsgaddcmds,
                        "$SYMCLI/symaccess -sid $emcfg{partner_sid} -type storage -name $this_sg add devs $sg_devlist" );
                }
            }
        }
    }
    return @dgsgaddcmds;
}

sub emc_run_vmax_auto {
    ## Creates auto provisioning groups for vmax
    ## called by emc_main
    ## app-FA_FA_view => {app-FA-FA_pg , app-FA-FA_sg , app-FA-FA_ig }
    ##     app-FA-FA_pg => fa:port, fa:port
    ##     app-FA-FA_sg => DEV,DEV,DEV,DEV,DEV
    ##     app-FA-FA_ig => host_hba_ig , host_hba_ig
    ##          host_hba_ig => WWN
    my @autocmds = ();     ## Holds all commands required for auto provisioning
    my @check_new =  ();   ## Holds the storage group return array, if it's empty then it's an upgrade, otherwise it's a new allocation
    my $doing_anything = 0; ## Tracks if we actually had any auto provisioning work to do, or if it's just headers

    ## Variables for DG array
    my @dgautocmds = ();
    my @dgcheck_new =  ();
    my $dgdoing_anything = 0;

    ## Get Existing Auto Provisioning groups
    emc_get_existing_auto($emcfg{sid});

    ## Saves our filename as CASE_NAME_FUNCTION_YYMMDD_SESSIONID    e.g. 12345_cs99-db_auto_20120201_999.sh
    $emcfg{autofile} = "$emcfg{sfdc}" . "_$emcopts{name}" . "_auto_" . shortdate . "_$emcfg{sessionid}" . ".sh";

    ## Human Header ##
    push ( @autocmds, "## Execute this file as shell script : 'sudo ./$emcfg{autofile}'" );
    push ( @autocmds, "## " . logtime . " Created automatically via $0" );
    push ( @autocmds, "##" );

    ## Constarnation Header .. symaccess won't provide any usable output
    push ( @autocmds, "##Constarnation:CMD:553:./$emcfg{autofile}" );

    if ( $emcopts{'3dc'} ) {
        emc_get_existing_auto($emcfg{partner_sid});
        $emcfg{dgautofile} = "$emcfg{sfdc}" . "_$emcopts{dgname}" . "_auto_" . shortdate . "_$emcfg{sessionid}" . ".sh";
        push ( @dgautocmds, "## Execute this file as shell script : 'sudo ./$emcfg{dgautofile}'" );
        push ( @dgautocmds, "## " . logtime . " Created automatically via $0" );
        push ( @dgautocmds, "##" );
        push ( @dgautocmds, "##Constarnation:CMD:583:./$emcfg{dgautofile}" );
    }

    ## Create Storage Groups .. We are checking first because if we get back an empty Array we know this is an upgrade rather than a new allocation
    my ($array1_ref, $array2_ref) = emc_create_sg();
    @check_new   = @$array1_ref;
    @dgcheck_new = @$array2_ref;

    ## If it's a new auto provisioning group
    if (@check_new) {
        ## We are doing something
        $doing_anything++;

        ## Start with the storage groups
        @autocmds = ( @autocmds, @check_new );

        ## Create Initiator Groups
        @autocmds = ( @autocmds, emc_create_ig );

        ## Create Port Groups
        @autocmds = ( @autocmds, emc_create_pg );

        ## Create Views
        @autocmds = ( @autocmds, emc_create_view );
    }

    ## Else we need to find our storage groups and just add the new storage to them
    else {
        ## Make sure we didn't get another empty array back
        @check_new = emc_add_to_sg;

        if (@check_new) {
            $doing_anything++;
            @autocmds = ( @autocmds, @check_new );
        }
    }

    if ( $emcopts{'3dc'} ) {
        if (@dgcheck_new) {
            ## We are doing something
            $dgdoing_anything++;

            ## Start with the storage groups
            @dgautocmds = ( @dgautocmds, @dgcheck_new );

            ## Create Initiator Groups
            @dgautocmds = ( @dgautocmds, emc_create_ig_dg );

            ## Create Port Groups
            @dgautocmds = ( @dgautocmds, emc_create_pg_dg );

            ## Create Views
            @dgautocmds = ( @dgautocmds, emc_create_view_dg );
        }

        ## Else we need to find our storage groups and just add the new storage to them
        else {
            ## Make sure we didn't get another empty array back
            @dgcheck_new = emc_add_to_sg_dg;

            if (@dgcheck_new) {
                $dgdoing_anything++;
                @dgautocmds = ( @dgautocmds, @dgcheck_new );
            }
        }
    }
    ## Create Auto Provisioning File
    if ($doing_anything) { create_output_file ( $emcfg{autofile}, $emcfg{user_uid}, @autocmds ); }
    else                 { emc_status ( "warn", "Doesn't appear to be any auto provisioning work to do." ); }
    ## For DG Array
    if ($dgdoing_anything) { create_output_file ( $emcfg{dgautofile}, $emcfg{user_uid}, @dgautocmds ); }
    else                 { emc_status ( "warn", "Doesn't appear to be any auto provisioning work to do." ); }
}

##########
## Main ##
##########
$SIG{INT} = \&sig_bailout;

sub emc_main {
    ## Only run if we call this via script
    check_root;    ## Makes sure we are running as root
    $emcfg{this_script} = abs_path ($0);    ## Sets the absolute path to this script
    get_user ( \%emcfg );                   ## Gets the running user and stores in $emcfg{user}
    emc_parse_opts;                         ## Gets and parses CLI options
    set_session_id ( \%emcfg );             ## sets the $emcfg{sessionid} to the current PID, used for logs and names
    emc_status ( "INFO", "Session ID $emcfg{sessionid}" );
    emc_set_array_info;                     ## verifies the serial number and sets $emcfg{sid}, $emcfg{array_type} & $emcfg{ecode_vers}

    ## If we are EXECUTING SRDF commands
    if ( defined $emcopts{exec_srdf} ) {
        emc_run_exec_srdf;
    }

    ## Else we are executing everything else
    else {
        ## Create devicelist, used by many subs.
        foreach my $key ( sort keys %device_info_list ) {
            push ( @devlist, $key );
        }

        ## Pulls detailed device all at one time if we are going to call any of the functions that need it
        ## This is determined at the end of emc_parse_opts()
        if ( $emcfg{need_dev_detail} ) {
            emc_verify_devices ($emcfg{sid}, @devlist);
            if ( $emcopts{'3dc'} ) {
                emc_verify_devices ($emcfg{partner_sid}, @devlist);
            }
        }

        ## Run DMX commands ##
        if ( ( defined $emcfg{array_type} ) && ( $emcfg{array_type} =~ m/DMX/ ) ) {
            ## Run DMX Commands
            if ( defined $emcopts{meta} ) {
                if   ( defined $emcopts{meta_width} ) { emc_run_metas ( $emcopts{meta_width}, @devlist ); }
                else                                  { emc_run_metas ( 16,                   @devlist ); }
            }
            if ( defined $emcopts{convert} )     { emc_run_convert     (@devlist); }
            if ( defined $emcopts{map} )         { emc_run_dmx_map; }
            if ( defined $emcopts{alias} )       { emc_run_alias; }
            if ( defined $emcopts{mask} )        { emc_run_dmx_mask; }
            if ( defined $emcopts{clone} )       { emc_run_clone       (@devlist); }
            if ( defined $emcopts{replication} ) { emc_run_replication ("false", @devlist); }
            if ( defined $emcopts{symdg} )       { emc_run_symdg       (@devlist); }
        }

        ## Run VMAX commands
        elsif ( ( defined $emcfg{array_type} ) && ( $emcfg{array_type} =~ m/VMAX/ ) ) {
            ## Run vmax commands.. Since -map, -mask, -alias all mean the same thing in vmax world, we'll run the same subroutine if any of them are called
            if ( ( $emcfg{array_type} ne "VMAX100K" ) && ( $emcfg{array_type} ne "VMAX200K" ) && ( defined $emcopts{meta} ) ) { #VMAX3 has NO metas
                if   ( defined $emcopts{meta_width} ) { emc_run_metas ( $emcopts{meta_width}, @devlist ); }
                else                                  { emc_run_metas ( 16,                   @devlist ); }
            }
            if ( defined $emcopts{convert} ) { emc_run_convert (@devlist); }
            if ( ( defined $emcopts{map} ) || ( defined $emcopts{mask} ) ) { emc_run_vmax_auto; }
            if ( defined $emcopts{alias} )       { emc_run_alias;
                                                 if ( $emcopts{'3dc'} ) { emc_run_alias_dg; }
                                                 }
            if ( defined $emcopts{clone} )       { emc_run_clone (@devlist); }
            if ( defined $emcopts{replication} ) {
                if ( (defined $emcopts{format} ) && ( defined $emcfg{ecode_vers} ) && ( $emcfg{ecode_vers} >= 5876 ) )
                                                 { emc_run_replication ("true", @devlist);
                                                 if ( $emcopts{'3dc'} ) {
                                                      emc_run_replication_dg("true", @devlist); }}
                  else                           { emc_run_replication ("false", @devlist);
                                                 if ( $emcopts{'3dc'} ) {
                                                      emc_run_replication_dg("false", @devlist); }}
            }
            if ( defined $emcopts{symdg} )       { emc_run_symdg (@devlist);
                                                 if ( $emcopts{'3dc'} ) {
                                                      emc_run_symdg_dg(@devlist); }}
        }

        ## Not a DMX or VMAX, lets bail
        else { bailout ( 10, "Array type $emcfg{array_type} not supported" ); }

    }
    list_scriptrunner;    ## Writes out all the files we created for scriptrunner parsing
    emc_write_logfile;
    exit 0;               ## Made it to the end if we ran as a script, exit cleanly
}

## Allows this to be included as a module, will run emc_main only if run as a script
emc_main () unless caller;
